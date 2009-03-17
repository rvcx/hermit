// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.hierarchy;

import java.util.Map;
import java.util.Set;
import java.util.HashSet;
import java.util.ArrayList;
import java.util.Iterator;
import org.semanticweb.HermiT.util.GraphUtils;
import org.semanticweb.HermiT.util.InducedSubgraph;

public class Taxonomy<T> {
    public Map<T, T> canonical;
    public Map<T, Set<T>> equivs;
    public Map<T, Set<T>> reduced;
    public Map<T, Set<T>> reduced_inverse;
    public Map<T, Set<T>> closed;
    public Map<T, Set<T>> closed_inverse;
    
    /**
     * Prune possible information based on the (partial) information stored
     * in `this`.
     * 
     * A relation `u -> v` is possible only if for every ancestor `u1` of
     * `u` and every descendant `v1` of `v`, the relation `u1 -> v1` is
     * possible.
     */
    private void prunePossibles(Map<T, Set<T>> possibleSuccessors) {
        // possible subsumers must be possible for every equivalent:
        for (Map.Entry<T, T> e : canonical.entrySet()) {
            Set<T> oldnameSuccs = possibleSuccessors.get(e.getKey());
            if (oldnameSuccs != null) {
                Set<T> canonicalSuccs = possibleSuccessors.get(e.getValue());
                if (canonicalSuccs != null) {
                    canonicalSuccs.retainAll(oldnameSuccs);
                } else {
                    possibleSuccessors.put
                        (e.getValue(), new HashSet<T>(oldnameSuccs));
                }
            }
        }
        
        // Prune based on known relationships:
        for (T u : GraphUtils.topologicalSort(reduced)) {
            Set<T> uPoss = possibleSuccessors.get(u);
            for (T uprime : reduced_inverse.get(u)) {
                // only need to look at reduced due to topological ordering
                Set<T> uprimePoss = possibleSuccessors.get(uprime);
                if (uprimePoss != null) {
                    if (uPoss != null) {
                        uPoss.retainAll(uprimePoss);
                    } else {
                        uPoss = new HashSet<T>(uprimePoss);
                        possibleSuccessors.put(u, uPoss);
                    }
                }
            }
            if (uPoss != null) {
                for (T v : new ArrayList<T>(uPoss)) {
                    if (!uPoss.containsAll(closed.get(v))) {
                        uPoss.remove(v);
                    }
                }
            }
        }
    }
    
    /**
     * Prune possible information based on the knowledge that all successors
     * of `t` are listed in `this.closed`.
     * 
     * A relation `u -> v` is possible only if for every ancestor `u1` of
     * `u` and every descendant `v1` of `v`, the relation `u1 -> v1` is
     * possible.
     */
    private void prunePossibles(T t,
                                Map<T, Set<T>> poss,
                                Map<T, Set<T>> poss_inv) {
        // Consider the information gained from each previous possible
        // successor of `t`:
        Set<T> oldPoss = poss.get(t);
        poss.put(t, new HashSet<T>(GraphUtils.successors(t, closed)));
        for (T p : oldPoss) {
            if (GraphUtils.successors(t, closed).contains(p)) {
                // The old possible became a known:
                { // Cases where the new edge serves as `u1 -> u`:
                    final T u1 = t, u = p;
                    for (Iterator<T> uv = poss.get(u).iterator();
                         uv.hasNext(); ) {
                        T v = uv.next();
                        if (!poss.get(u1).containsAll
                                (GraphUtils.successors(v, closed))) {
                            uv.remove();
                            poss_inv.get(v).remove(u);
                        }
                    }
                }
                { // Cases where the new edge serves as `v -> v1`:
                    final T v = t, v1 = p;
                    for (Iterator<T> vu = poss_inv.get(v).iterator();
                         vu.hasNext(); ) {
                        T u = vu.next();
                        if (!poss_inv.get(v1).containsAll
                                (GraphUtils.successors(u, closed_inverse))) {
                            vu.remove();
                            poss.get(u).remove(v);
                        }
                    }
                }
            } else { // An edge is no longer considered possible:
                final T u1 = t, v1 = p;
                for (T u : GraphUtils.successors(u1, closed)) {
                    for (Iterator<T> uv = poss.get(u).iterator();
                         uv.hasNext(); ) {
                        T v = uv.next();
                        if (GraphUtils.successors(v, closed).contains(v1)) {
                            uv.remove();
                            poss_inv.get(v).remove(u);
                        }
                    }
                }
            } // end else
        } // end loop over (old) possible edges
        assert poss.get(t).isEmpty();
    }

    private interface Predicate<T> {
        boolean trueOf(T t);
    }
    
    /**
     * Return the vertices of `graph` for which `predicate.trueOf` returns
     * `true`, and which have no ancestors for which `predicate.trueOf`
     * returns `true`.
     * 
     * The given predicate must be inherited through the graph: if it is true
     * of a vertex `v` then it must also be true of all successors of `v`.
     */
    private static <T> Set<T> mostGeneral(final Predicate<T> predicate,
                                          final Map<T, Set<T>> graph,
                                          Map<T, Set<T>> inverse) {
        Predicate<T> cachedPredicate = new Predicate<T>() {
            Map<T, Boolean> cache;
            boolean compute(T v) {
                for (T w : GraphUtils.successors(v, graph)) {
                    if (!this.trueOf(w)) return false;
                }
                return predicate.trueOf(v);
            }
            public boolean trueOf(T v) {
                if (!cache.containsKey(v)) {
                    cache.put(v, new Boolean(compute(v)));
                }
                return cache.get(v).booleanValue();
            }
        };
        
        Set<T> leaves = new HashSet<T>(inverse.keySet());
        for (Map.Entry<T, Set<T>> e : graph.entrySet()) {
            if (!e.getValue().isEmpty()) {
                leaves.remove(e.getKey());
            }
        }
        
        Set<T> visited = new HashSet<T>();
        for (T t : leaves) {
            if (cachedPredicate.trueOf(t)) {
                visited.add(t);
            }
        }
        Set<T> q = new HashSet<T>(visited);
        Set<T> out = new HashSet<T>();
        while (!q.isEmpty()) {
            T t = q.iterator().next();
            q.remove(t);
            boolean foundAnother = false;
            for (T predecessor : GraphUtils.successors(t, inverse)) {
                if (cachedPredicate.trueOf(predecessor)) {
                    if (visited.add(predecessor)) {
                        q.add(predecessor);
                    }
                    foundAnother = true;
                }
            }
            if (!foundAnother) {
                out.add(t);
            }
        }
        return out;
    }

    private Set<T> newSuccessors(final T t,
                                 final Predicate<T> succTest,
                                 Map<T, Set<T>> possible) {
        Set<T> toConsider = new HashSet<T>(possible.get(t));
        toConsider.removeAll(GraphUtils.successors(t, closed));
        return mostGeneral(
            succTest,
            new InducedSubgraph<T>(reduced, toConsider),
            new InducedSubgraph<T>(reduced_inverse, toConsider));
    }
    
    private void updateClosure(T t, Set<T> newSuccessors) {
        // Update closure (which serves as "known" information):
        Set<T> closedSuccs = GraphUtils.successorSet(t, closed);
        for (T succ : newSuccessors) {
            GraphUtils.successorSet(succ, closed_inverse)
                .addAll(GraphUtils.successors(t, closed_inverse));
            closedSuccs.addAll(GraphUtils.successors(succ, closed));
        }
        for (T pred : GraphUtils.successors(t, closed_inverse)) {
            closed.get(t).addAll(closedSuccs);
        }
    }
    
    private Taxonomy(Taxonomy<T> inverse) {
        canonical = inverse.canonical;
        equivs = inverse.equivs;
        reduced = inverse.reduced_inverse;
        reduced_inverse = inverse.reduced;
        closed = inverse.closed_inverse;
        closed_inverse = inverse.closed;
    }
    
    public interface Ordering<U> {
        boolean doesPrecede(U predecessor, U successor);
    }

    public Taxonomy(final Ordering<? super T> order,
                    Map<T, Set<T>> knownSuccessors, // can't be null
                    Map<T, Set<T>> possibleSuccessors) {
        assert knownSuccessors != null;
        assert GraphUtils.isSubgraphOf(knownSuccessors, possibleSuccessors);
        
        GraphUtils.Acyclic<T> acyc
            = new GraphUtils.Acyclic<T>(knownSuccessors);
        canonical = acyc.canonical;
        equivs = acyc.equivs;
        GraphUtils.TransAnalyzed<T> analyzed
            = new GraphUtils.TransAnalyzed<T>(acyc.graph);
        reduced = analyzed.reduced;
        reduced_inverse = GraphUtils.reversed(reduced);
        closed = analyzed.closed;
        closed_inverse = GraphUtils.reversed(closed);
        
        prunePossibles(possibleSuccessors);
        
        Map<T, Set<T>> poss = possibleSuccessors;
        Map<T, Set<T>> poss_inv = GraphUtils.reversed(poss);
        
        Taxonomy<T> tax_inv = new Taxonomy<T>(this);

        for (T t : closed.keySet()) { // might want to sort this...
            final T finalT = t;
            Set<T> succs = newSuccessors
                (t,
                 new Predicate<T>() {
                     public boolean trueOf(T u) {
                         return order.doesPrecede(finalT, u);
                     }
                 },
                 poss);
            updateClosure(t, succs);
            prunePossibles(t, poss, poss_inv);
            
            Set<T> preds = tax_inv.newSuccessors
                (t,
                 new Predicate<T>() {
                     public boolean trueOf(T u) {
                         return order.doesPrecede(u, finalT);
                     }
                 },
                 poss_inv);
            tax_inv.updateClosure(t, preds);
            tax_inv.prunePossibles(t, poss_inv, poss);
            
            // Update reduced:
            if (succs.equals(preds)) {
                assert succs.size() == 1 && preds.size() == 1;
                T tCanonical = succs.iterator().next();
                Set<T> eqClass = equivs.get(canonical);
                eqClass.addAll(equivs.get(t));
                for (T equiv : equivs.get(t)) {
                    canonical.put(equiv, tCanonical);
                    equivs.put(equiv, eqClass);
                }
                succs = GraphUtils.successors(t, reduced);
                preds = GraphUtils.successors(t, reduced_inverse);
                t = tCanonical;
            }
            Set<T> tSuccs = GraphUtils.successorSet(t, reduced);
            for (T succ : succs) {
                tSuccs.removeAll(GraphUtils.successors(succ, closed));
                tSuccs.add(succ);
                Set<T> sPreds = GraphUtils.successorSet(succ, reduced_inverse);
                sPreds.removeAll(GraphUtils.successors(t, closed_inverse));
                sPreds.add(t);
            }
            Set<T> tPreds = GraphUtils.successorSet(t, reduced_inverse);
            for (T pred : preds) {
                tPreds.removeAll(GraphUtils.successors(pred, closed_inverse));
                tPreds.add(pred);
                Set<T> pSuccs = GraphUtils.successorSet(pred, reduced);
                pSuccs.removeAll(GraphUtils.successors(t, closed));
                pSuccs.add(t);
            }
        }
    }
    
    Position getPosition(final Hierarchy.Element<T> element,
                         Set<T> knownSuccessors,
                         Set<T> possibleSuccessors,
                         Set<T> knownPredecessors,
                         Set<T> possiblePredecessors) {
        return new Position(element,
                            knownSuccessors,
                            possibleSuccessors,
                            knownPredecessors,
                            possiblePredecessors);
    }
    
    public class Position {
        public Set<T> successors;
        public Set<T> predecessors;
        public Position(final Hierarchy.Element<T> element,
                        Set<T> knownSuccessors,
                        Set<T> possibleSuccessors,
                        Set<T> knownPredecessors,
                        Set<T> possiblePredecessors) {
            T equiv = element.getEquivalent();
            if (equiv != null && canonical.containsKey(equiv)) {
                equiv = canonical.get(equiv);
                successors = GraphUtils.successors(equiv, reduced);
                predecessors = GraphUtils.successors(equiv, reduced_inverse);
                return;
            }
            assert knownSuccessors == null
                || possibleSuccessors == null
                || possibleSuccessors.containsAll(knownSuccessors);
            assert knownPredecessors == null
                || possiblePredecessors == null
                || possiblePredecessors.containsAll(knownPredecessors);
            
            // Extend known:
            if (knownSuccessors != null) {
                for (T succ : new ArrayList<T>(knownSuccessors)) {
                    knownSuccessors.addAll(closed.get(succ));
                }
            }
            if (knownPredecessors != null) {
                for (T pred : new ArrayList<T>(knownPredecessors)) {
                    knownPredecessors.addAll(closed_inverse.get(pred));
                }
            }

            // Prune possible successors:
            if (knownPredecessors != null && possibleSuccessors != null) {
                for (T pred : knownPredecessors) {
                    possibleSuccessors.retainAll(closed.get(pred));
                }
            }
            
            // Find successors:
            Set<T> toConsider = new HashSet<T>(closed.keySet());
            if (possibleSuccessors != null) {
                toConsider.retainAll(possibleSuccessors);
            }
            if (knownSuccessors != null) {
                toConsider.removeAll(knownSuccessors);
            }
            successors = mostGeneral(
                new Predicate<T>() {
                    public boolean trueOf(T u) {
                        return element.doesPrecede(u);
                    }
                },
                new InducedSubgraph<T>(reduced, toConsider),
                new InducedSubgraph<T>(reduced_inverse, toConsider));
            if (knownSuccessors != null) {
                for (T succ : successors) {
                    knownSuccessors.removeAll(closed.get(succ));
                }
                successors.addAll(knownSuccessors);
            }
            
            
            // Prune possible predecessors:
            if (possiblePredecessors != null) {
                for (T succ : successors) {
                    possiblePredecessors
                        .retainAll(closed_inverse.get(succ));
                }
            }

            // Find predecessors:
            toConsider = new HashSet<T>(closed.keySet());
            if (possiblePredecessors != null) {
                toConsider.retainAll(possiblePredecessors);
            }
            if (knownPredecessors != null) {
                toConsider.removeAll(knownPredecessors);
            }
            predecessors = mostGeneral(
                new Predicate<T>() {
                    public boolean trueOf(T u) {
                        return element.doesSucceed(u);
                    }
                },
                new InducedSubgraph<T>(reduced_inverse, toConsider),
                new InducedSubgraph<T>(reduced, toConsider));
            if (knownPredecessors != null) {
                for (T pred : predecessors) {
                    knownPredecessors.removeAll(closed_inverse.get(pred));
                }
                predecessors.addAll(knownPredecessors);
            }
        }
    }
}
