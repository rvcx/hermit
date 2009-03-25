// Copyright 2009 by Rob Shearer; see license.txt for details
package org.semanticweb.HermiT.hierarchy;

import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;
import java.util.List;
import java.util.Collections;
import java.util.ArrayList;
import java.util.Iterator;
import org.semanticweb.HermiT.util.GraphUtils;
import org.semanticweb.HermiT.util.InducedSubgraph;
import org.semanticweb.HermiT.util.DifferenceSet;

import org.semanticweb.HermiT.util.GraphTesting;
import org.semanticweb.HermiT.util.TaskStatus;
import org.semanticweb.HermiT.util.NullMonitor;
import org.semanticweb.HermiT.util.ConsoleMonitor;

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
                    assert false;
                    possibleSuccessors.put(e.getValue(), oldnameSuccs);
                }
            }
        }
        
        // Prune based on known relationships:
        for (T u : GraphUtils.topologicalSort(reduced)) {
            Set<T> uPoss = possibleSuccessors.get(u);
            for (T uprime : GraphUtils.successors(u, reduced_inverse)) {
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
                    if (!uPoss.containsAll(GraphUtils.successors(v, closed))) {
                        uPoss.remove(v);
                    }
                }
            }
        }
    }
    
    /**
     * Prune possible information based on the knowledge that all successors
     * of `t` are listed in `known`.
     * 
     * A relation `u -> v` is possible only if for every ancestor `u1` of
     * `u` and every descendant `v1` of `v`, the relation `u1 -> v1` is
     * possible.
     */
    private static <T> void prunePossibles(T t,
                                           Map<T, Set<T>> poss,
                                           Map<T, Set<T>> poss_inv,
                                           Map<T, Set<T>> known,
                                           Map<T, Set<T>> known_inverse) {
        // Consider the information gained from each previous possible
        // successor of `t`:
        Set<T> oldPoss = poss.get(t);
        poss.put(t, new HashSet<T>(GraphUtils.successors(t, known)));
        for (T p : oldPoss) {
            if (GraphUtils.successors(t, known).contains(p)) {
                // The old possible became a known:
                { // Cases where the new edge serves as `u1 -> u`:
                    final T u1 = t, u = p;
                    for (Iterator<T> uv = poss.get(u).iterator();
                         uv.hasNext(); ) {
                        T v = uv.next();
                        if (!poss.get(u1).containsAll
                                (GraphUtils.successors(v, known))) {
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
                                (GraphUtils.successors(u, known_inverse))) {
                            vu.remove();
                            poss.get(u).remove(v);
                        }
                    }
                }
            } else { // An edge is no longer considered possible:
                final T u1 = t, v1 = p;
                for (T u : GraphUtils.successors(u1, known)) {
                    for (Iterator<T> uv = poss.get(u).iterator();
                         uv.hasNext(); ) {
                        T v = uv.next();
                        if (GraphUtils.successors(v, known).contains(v1)) {
                            uv.remove();
                            poss_inv.get(v).remove(u);
                        }
                    }
                }
            } // end else
        } // end loop over (old) possible edges
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
            Map<T, Boolean> cache = new HashMap<T, Boolean>();
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
        leaves.addAll(graph.keySet());
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
        // TODO: see whether a FIFO queue works better in practice:
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

    private static <T> void extendClosure(T t, Set<T> newSuccessors,
                                          Map<T, Set<T>> closed,
                                          Map<T, Set<T>> closed_inverse) {
        Set<T> closedSuccs = GraphUtils.successorSet(t, closed);
        if (closedSuccs.containsAll(newSuccessors)) return;
        for (T succ : newSuccessors) {
            GraphUtils.successorSet(succ, closed_inverse)
                .addAll(GraphUtils.successors(t, closed_inverse));
            closedSuccs.addAll(GraphUtils.successors(succ, closed));
        }
        for (T succ : closedSuccs) {
            GraphUtils.successorSet(succ, closed_inverse)
                .addAll(GraphUtils.successors(t, closed_inverse));
        }
        for (T pred : GraphUtils.successors(t, closed_inverse)) {
            closed.get(pred).addAll(closedSuccs);
        }
    }
    
    private static <T> void extendReduced(T t, Set<T> newSuccessors,
                                          Map<T, Set<T>> reduced,
                                          Map<T, Set<T>> reduced_inverse,
                                          Map<T, Set<T>> closed,
                                          Map<T, Set<T>> closed_inverse) {
        // Remove old successors that are no longer direct:
        Set<T> defunctSuccs = new HashSet<T>();
        for (T succ : newSuccessors) {
            defunctSuccs.addAll(GraphUtils.successors(succ, closed));
        }
        defunctSuccs.retainAll(GraphUtils.successors(t, reduced));
        for (T oldSucc : defunctSuccs) {
            reduced.get(t).remove(oldSucc);
            reduced_inverse.get(oldSucc).remove(t);
        }
        // Add new successors:
        Set<T> redSuccs = GraphUtils.successorSet(t, reduced);
        Set<T> tPreds = GraphUtils.successors(t, closed_inverse);
        for (T succ : newSuccessors) {
            redSuccs.add(succ);
            Set<T> sPreds = GraphUtils.successorSet(succ, reduced_inverse);
            for (Iterator<T> i = sPreds.iterator(); i.hasNext(); ) {
                T sPred = i.next();
                if (tPreds.contains(sPred)) {
                    reduced.get(sPred).remove(succ);
                    i.remove();
                }
            }
            sPreds.add(t);
        }
    }
    
    public interface Ordering<U> {
        boolean doesPrecede(U predecessor, U successor);
    }

    public Taxonomy(final Ordering<? super T> order,
                    Set<T> domain,
                    Map<T, Set<T>> knownSuccessors, // can't be null
                    Map<T, Set<T>> possibleSuccessors,
                    TaskStatus status) {
        if (status == null) status = new NullMonitor();
        // Sanitize knownSuccessors and init taxonomy from known info:
        if (knownSuccessors == null) {
            knownSuccessors = new HashMap<T, Set<T>>();
        }
        GraphUtils.restrictToDomain(knownSuccessors, domain);
        for (T t : domain) {
            GraphUtils.successorSet(t, knownSuccessors).add(t);
        }
        
        TaskStatus analysisStatus
            = status.subTask("Analyzing known relationships");
        TaskStatus cur = analysisStatus.subTask("Removing cycles");
        GraphUtils.Acyclic<T> acyc
            = new GraphUtils.Acyclic<T>(knownSuccessors, true);
        cur.done();
        canonical = acyc.canonical;
        equivs = acyc.equivs;
        domain.retainAll(equivs.keySet());
        GraphUtils.TransAnalyzed<T> analyzed
            = new GraphUtils.TransAnalyzed<T>(acyc.graph,
                                        analysisStatus.subTask("Reducing"));
        reduced = analyzed.reduced;
        GraphUtils.removeSelfLoops(reduced);
        reduced_inverse = GraphUtils.reversed(reduced);
        for (T t : domain) {
            GraphUtils.successorSet(t, reduced);
            GraphUtils.successorSet(t, reduced_inverse);
            assert analyzed.closed.get(t).contains(t);
        }
        closed = analyzed.closed;
        closed_inverse = GraphUtils.reversed(closed);
        analysisStatus.done();
        
        assert closed.keySet().equals(domain);
        // if (!closed_inverse.keySet().equals(domain)) {
        //     System.err.println(domain.size());
        //     System.err.println(closed_inverse.keySet().size());
        //     assert false;
        // }
        assert closed_inverse.keySet().equals(domain);
        assert reduced.keySet().equals(domain);
        assert reduced_inverse.keySet().equals(domain);

        // Sanitize possibleSuccessors and prune based on known info:
        if (possibleSuccessors == null) {
            possibleSuccessors = new HashMap<T, Set<T>>();
        }
        for (Iterator<Map.Entry<T, Set<T>>> i
                = possibleSuccessors.entrySet().iterator();
             i.hasNext(); ) {
            Map.Entry<T, Set<T>> e = i.next();
            T can = canonical.get(e.getKey());
            if (can != null && domain.contains(can)) {
                e.getValue().retainAll(domain);
                e.getValue().addAll(closed.get(can));
            } else {
                i.remove();
            }
        }
        for (T t : domain) {
            if (!possibleSuccessors.containsKey(t)) {
                possibleSuccessors.put(t, new HashSet<T>(domain));
            }
        }
        TaskStatus possStatus
            = status.subTask("Preprocessing possible relationships");
        prunePossibles(possibleSuccessors);
        possStatus.done();
        for (Iterator<Map.Entry<T, Set<T>>> i
                = possibleSuccessors.entrySet().iterator();
             i.hasNext(); ) {
            if (!domain.contains(i.next().getKey())) {
                i.remove();
            }
        }
        Map<T, Set<T>> poss = possibleSuccessors;
        Map<T, Set<T>> poss_inv = GraphUtils.reversed(poss);

        // assert poss.keySet().equals(domain);
        // if (!poss_inv.keySet().equals(domain)) {
        //     Set<T> s = new HashSet<T>(poss_inv.keySet());
        //     System.err.println(s.size());
        //     System.err.println(domain.size());
        //     domain.removeAll(s);
        //     System.err.println(domain.size());
        //     // System.err.println(domain);
        //     assert false;
        // }
        // assert poss_inv.keySet().equals(domain);

        // Classify each concept:
        List<T> definitionOrder = GraphUtils.weakTopologicalSort(poss,
                            status.subTask("choosing classification order"));
        //Collections.reverse(definitionOrder);
        status.setNumSteps(definitionOrder.size());
        for (T t : definitionOrder) {
            status.step();
            
            // Skip an element if we already know everything about it:
            if (poss.get(t).equals(closed.get(t)) &&
                poss_inv.get(t).equals(closed_inverse.get(t))) continue;
            
            // Identify position in unknown portion of graph:
            final T finalT = t;
            Set<T> toConsider = new HashSet<T>(poss.get(t));
            toConsider.removeAll(GraphUtils.successors(t, closed));
            Set<T> succs = mostGeneral
                (new Predicate<T>() {
                     public boolean trueOf(T u) {
                         return order.doesPrecede(finalT, u);
                     }
                 },
                 new InducedSubgraph<T>(reduced, toConsider),
                 new InducedSubgraph<T>(reduced_inverse, toConsider));

            extendClosure(t, succs, closed, closed_inverse);
            prunePossibles(t, poss, poss_inv, closed, closed_inverse);
            
            toConsider = new HashSet<T>(poss_inv.get(t));
            toConsider.removeAll(GraphUtils.successors(t, closed_inverse));
            Set<T> preds = mostGeneral
                (new Predicate<T>() {
                     public boolean trueOf(T u) {
                         return order.doesPrecede(u, finalT);
                     }
                 },
                 new InducedSubgraph<T>(reduced_inverse, toConsider),
                 new InducedSubgraph<T>(reduced, toConsider));

            extendClosure(t, preds, closed_inverse, closed);
            prunePossibles(t, poss_inv, poss, closed_inverse, closed);
            
            // Update reduced:
            if (!succs.isEmpty() && succs.equals(preds)) {
                assert succs.size() == 1 && preds.size() == 1;
                T tCanonical = succs.iterator().next();
                Set<T> eqClass = equivs.get(canonical);
                eqClass.addAll(equivs.get(t));
                for (T equiv : equivs.get(t)) {
                    canonical.put(equiv, tCanonical);
                }
                equivs.remove(t);
                succs = GraphUtils.successors(t, reduced);
                preds = GraphUtils.successors(t, reduced_inverse);
                t = tCanonical;
            }
            
            extendReduced(t, succs,
                          reduced, reduced_inverse, closed, closed_inverse);
            extendReduced(t, preds,
                          reduced_inverse, reduced, closed_inverse, closed);
        }
        status.done();
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
    
    
    public static void main(String[] args) {
        
        GraphTesting.LadderGraph ladder = new GraphTesting.LadderGraph(50);
        
        java.util.Random rand = new java.util.Random(0);

        final GraphUtils.TransAnalyzed<Integer> correct
            = new GraphUtils.TransAnalyzed<Integer>(ladder.graph);
        GraphUtils.removeSelfLoops(correct.reduced);
        
        Ordering<Integer> order = new Ordering<Integer>() {
            public boolean doesPrecede(Integer x, Integer y) {
                return GraphUtils.successors(x, correct.closed).contains(y);
            }
        };
        
        Map<Integer, Set<Integer>> known = GraphTesting.cloneGraph(correct.closed);
        GraphTesting.removeEdges(known, 0.5, rand);
        Map<Integer, Set<Integer>> poss = GraphTesting.cloneGraph(correct.closed);
        GraphTesting.addEdges(poss, ladder.domain, 0.5, rand);
        
        Taxonomy<Integer> tax = new Taxonomy<Integer>(order, ladder.domain,
                                                      known, poss,
                        new ConsoleMonitor("Building taxonomy", System.err));
        
        if (!tax.reduced.equals(correct.reduced)) {
            System.out.println("Correct taxonomy:");
            GraphTesting.printGraph(correct.reduced, System.out);
            System.out.println("Computed taxonomy:");
            GraphTesting.printGraph(tax.reduced, System.out);
        } else {
            System.out.println("Woo-hoo!");
        }
        
    }
}
