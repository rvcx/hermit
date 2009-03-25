// Copyright 2009 by Rob Shearer; see license.txt for details
package org.semanticweb.HermiT.util;

import java.util.Map;
import java.util.TreeMap;
import java.util.HashMap;
import java.util.Set;
import java.util.TreeSet;
import java.util.HashSet;
import java.util.Collection;
import java.util.List;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Collections;
import java.util.Iterator;

public class GraphUtils {
    
    /**
     * Convenience function to get (an unmodifiable set of) the successors of
     * a vertex in a graph; if the vertex has no successors or does not appear
     * in the graph the empty set is returned.
     * 
     * Complexity: one set lookup
     */
    public static <T> Set<T> successors(T t, Map<T, Set<T>> graph) {
        Set<T> out = graph.get(t);
        if (out == null) {
            return Collections.emptySet();
        } else {
            return out;
        }
    }

    /**
     * Convenience function to return the modifiable set of successors of a
     * vertex, creating a new empty set if necessary.
     * 
     * Complexity: one set lookup
     */
    public static <T> Set<T> successorSet(T t, Map<T, Set<T>> graph) {
        Set<T> out = graph.get(t);
        if (out == null) {
            out = new HashSet<T>();
            graph.put(t, out);
        }
        return out;
    }

    /**
     * Use a simple algorithm to compute the transitive closure of a graph in
     * place. For more sophisticated handling of transitively check out the
     * `TransAnalyzed` class below.
     * 
     * Complexity: O(n^3) worst-case (use `TransAnalyzed` for tighter bounds)
     */
    public static <T> void transitivelyClose(Map<T, Set<T>> relation) {
        // We follow the outline of Warshall's algorithm, which runs in O(n^3),
        // but do our best to avoid the cubic blowup if we can:
        HashSet<T> toProcess = new HashSet<T>();
        for (Set<T> reachable : relation.values()) {
            toProcess.clear();
            toProcess.addAll(reachable);
            toProcess.retainAll(relation.keySet());
            while (!toProcess.isEmpty()) {
                // In the worst case we end up visiting every possible value.
                T intermediate = toProcess.iterator().next();
                toProcess.remove(intermediate);
                for (T fresh : relation.get(intermediate)) {
                    if (reachable.add(fresh) &&
                        relation.containsKey(fresh)) {
                        toProcess.add(fresh);
                    }
                }
            }
        }
    } // end transitivelyClose
    
    /**
     * A comparator which uses a given ordering as the sort order for all
     * elements. This is useful in cases where there is no natural ordering
     * for a type but a consistent ordering of a known set of elements is
     * required.
     * 
     * Complexity: creation of the comparator is linear; comparisons require
     * two lookups in a set containing all elements.
     */
    public static class CompareByPosition<T> implements Comparator<T> {
        private Map<T, Integer> positions = new HashMap<T, Integer>();
        public CompareByPosition(Collection<T> order) {
            int i = 0;
            for (T t : order) {
                positions.put(t, new Integer(i++));
            }
        }
        public CompareByPosition(Map<T, Integer> positions) {
            this.positions = positions;
        }
        public int compare(T o1, T o2) {
            // We sort any values not in the original ordering last:
            Integer i1 = positions.get(o1);
            Integer i2 = positions.get(o2);
            if (i1 != null && i2 != null) {
                return i1.compareTo(i2);
            } else if (i1 != null) {
                return -1;
            } else if (i2 != null) {
                return 1;
            } else {
                return 0;
            }
        }
        @SuppressWarnings("unchecked")
        public boolean equals(Object obj) {
            return (obj instanceof CompareByPosition &&
                    ((CompareByPosition) obj).positions.equals(positions));
        }
    } // end class CompareByPosition
    
    /**
     * Return the inverse of a graph; i.e. if `v` is a successor of `u` in
     * `graph`, then `u` is a successor of `v` in the returned graph.
     * 
     * Complexity: linear in the number of edges of the graph
     */
    public static <T> Map<T, Set<T>> reversed(Map<T, Set<T>> graph) {
        Map<T, Set<T>> out = new HashMap<T, Set<T>>();
        for (Map.Entry<T, Set<T>> e : graph.entrySet()) {
            for (T t : e.getValue()) {
                Set<T> tPred = out.get(t);
                if (tPred == null) {
                    tPred = new HashSet<T>();
                    out.put(t, tPred);
                }
                tPred.add(e.getKey());
            }
        }
        return out;
    } // end reversed
    
    /**
     * Prune the given map of elements with empty values. On return `graph`
     * will contain only keys with at least one successor.
     * 
     * Complexity: linear in the number of vertices of the graph
     */
    public static <T> void pruneEmpty(Map<T, Set<T>> graph) {
        Collection<T> toPrune = new ArrayList<T>();
        for (Map.Entry<T, Set<T>> e : graph.entrySet()) {
            if (e.getValue().isEmpty()) {
                toPrune.add(e.getKey());
            }
        }
        for (T t : toPrune) {
            graph.remove(t);
        }
    }
    
    public static <T> void removeSelfLoops(Map<T, Set<T>> graph) {
        for (Map.Entry<T, Set<T>> e : graph.entrySet()) {
            e.getValue().remove(e.getKey());
        }
    }
    
    public static <T> void makeReflexive(Map<T, Set<T>> graph,
                                         Set<T> domain) {
        for (T t : domain) {
            successorSet(t, graph).add(t);
        }
    }
    
    /**
     * Return a topological ordering of an graph with no cycles other than
     * self-loops; i.e. if `v` is a successor of `u` in `graph` then `u` will
     * precede `v` in the returned list.
     * 
     * Complexity: O(|V| + |E|)
     */
    public static <T> List<T> topologicalSort(Map<T, Set<T>> graph) {
        return topologicalSort(graph, new NullMonitor());
    }
    public static <T> List<T> topologicalSort(Map<T, Set<T>> graph,
                                              TaskStatus status) {
        List<T> out = new ArrayList<T>();
        Map<T, Set<T>> incoming = reversed(graph);
        removeSelfLoops(incoming);
        pruneEmpty(incoming);
        Set<T> noIncoming = new HashSet<T>(graph.keySet());
        noIncoming.removeAll(incoming.keySet());
        status.setNumSteps(incoming.size() + noIncoming.size());
        while (!noIncoming.isEmpty()) {
            status.step();
            Iterator<T> i = noIncoming.iterator();
            T t = i.next();
            i.remove();
            out.add(t);
            for (T succ : successors(t, graph)) {
                if (succ.equals(t)) continue;
                Set<T> succIncoming = incoming.get(succ);
                assert succIncoming != null;
                assert succIncoming.contains(t);
                succIncoming.remove(t);
                if (succIncoming.isEmpty()) {
                    incoming.remove(succ);
                    noIncoming.add(succ);
                }
            }
        }
        status.done();
        if (!incoming.isEmpty()) {
            throw new IllegalArgumentException
                ("Unable to topologically sort a graph containing cycles.");
        }
        return out;
    } // end topologicalSort
    
    /**
     * Return a linearization of a graph which is not necessarily acyclic.
     */
    public static <T> List<T> weakTopologicalSort(Map<T, Set<T>> graph) {
        return weakTopologicalSort(graph, new NullMonitor());
    }
    public static <T> List<T> weakTopologicalSort(Map<T, Set<T>> graph,
                                                  TaskStatus status) {
        Acyclic<T> acyc = new Acyclic<T>(graph, false);
        List<T> out = new ArrayList<T>();
        for (T canonical : topologicalSort(acyc.graph, status.subTask("sorting"))) {
            out.addAll(acyc.equivs.get(canonical));
        }
        return out;
    }

    /**
     * Create an acyclic version of a graph by replacing every cycle with
     * a single (arbitrarily chosen) canonical vertex to represent the cycle.
     * 
     * The constructor for the class does all the work, with the result stored
     * in the object's (public) members.
     */
    public static class Acyclic<T> {
        /**
         * An acyclic graph, with a single vertex chosen to represent each
         * cycle from the original graph.
         */
        public Map<T, Set<T>> graph = new HashMap<T, Set<T>>();

        /**
         * A map from each vertex of the original graph to that vertex's
         * representative in the acyclic graph.
         */
        public Map<T, T> canonical = new HashMap<T, T>();
        
        /**
         * A map from each vertex of the acyclic graph to the set of vertices
         * of the original graph it represents.
         */
        public Map<T, Set<T>> equivs = new HashMap<T, Set<T>>();
        
        public Acyclic(Map<T, Set<T>> graph, boolean retainSelfLoops) {
            for (Set<T> scc : sccs(graph)) {
                assert !scc.isEmpty();
                T canon = scc.iterator().next();
                equivs.put(canon, scc);
                for (T t : scc) {
                    canonical.put(t, canon);
                }
            }
            for (Map.Entry<T, Set<T>> e : graph.entrySet()) {
                T t = canonical.get(e.getKey());
                Set<T> acycSuccessors = this.graph.get(t);
                for (T succ : e.getValue()) {
                    succ = canonical.get(succ);
                    if (succ != t || retainSelfLoops) {
                        if (acycSuccessors == null) {
                            acycSuccessors = new HashSet<T>();
                            this.graph.put(t, acycSuccessors);
                        }
                        acycSuccessors.add(succ);
                    }
                }
            }
        } // end constructor
    } // end class Acyclic
    
    /**
     * Compute the transitive reduction and transitive closure of a graph.
     * 
     * The constructor for the class does all the work, with the results
     * stored in the object's (public) members.
     */
    public static class TransAnalyzed<T> {
        public Map<T, Set<T>> reduced = new HashMap<T, Set<T>>();
        public Map<T, Set<T>> closed = new HashMap<T, Set<T>>();
        public TransAnalyzed(Map<T, Set<T>> graph) {
            this(graph, new NullMonitor());
        }
        
        public TransAnalyzed(Map<T, Set<T>> graph, TaskStatus status) {
            List<T> order = topologicalSort(graph, status.subTask("sorting"));
            Comparator<T> cmp = new CompareByPosition<T>(order);
            Collections.reverse(order);
            TaskStatus analyzing = status.subTask("analyzing");
            analyzing.setNumSteps(order.size());
            for (T t : order) {
                analyzing.step();
                Set<T> reached = new HashSet<T>();
                Set<T> tSucc = graph.get(t);
                if (tSucc != null) {
                    Set<T> reducedSucc = successorSet(t, reduced);
                    Set<T> closedSucc = successorSet(t, closed);
                    List<T> successors = new ArrayList<T>(tSucc);
                    Collections.sort(successors, cmp);
                    for (T succ : successors) {
                        if (!reached.contains(succ)) {
                            closedSucc.add(succ);
                            reducedSucc.add(succ);
                            Set<T> reachable = closed.get(succ);
                            if (reachable != null) {
                                for (T desc : reachable) {
                                    if (!reached.contains(desc)) {
                                        reached.add(desc);
                                        closedSucc.add(desc);
                                    }
                                }
                            }
                        }
                    } // end for succ
                } // end if tSucc
            } // end for t
            analyzing.done();
            status.done();
        } // end constructor
    } // end class TransAnalyzed
    
    /**
     * Explore a graph depth-first, recording the order in which vertices
     * were first and last visited, as well as the edge used to visit each
     * vertex. The algorithm is from Cormen, Leiserson, and Rivest.
     * 
     * This is really just used as a utility within computation of strongly-
     * connected components.
     */
    static class DepthFirstSearch<T> {
        public Map<T, Integer> discovered = new HashMap<T, Integer>();
        public Map<T, Integer> finished = new HashMap<T, Integer>();
        public Map<T, T> predecessor = new HashMap<T, T>();
        int totalTime = 0;
        
        public DepthFirstSearch(Map<T, Set<T>> graph, Collection<T> order) {
            if (order == null) {
                order = graph.keySet();
            }
            for (T t : order) {
                if (!discovered.containsKey(t)) {
                    visit(t, graph);
                }
            }
        }
        
        private void visit(T t, Map<T, Set<T>> graph) {
            discovered.put(t, new Integer(++totalTime));
            Set<T> successors = graph.get(t);
            if (successors != null) {
                for (T u : successors) {
                    if (!discovered.containsKey(u)) {
                        predecessor.put(u, t);
                        visit(u, graph);
                    }
                }
            }
            finished.put(t, new Integer(++totalTime));
        }
    }
    
    /**
     * Return the strongly-connected components of a graph.
     * The algorithm is from Cormen, Leiserson, and Rivest.
     * 
     * Complexity: O(|V| + |E|)
     */
    static <T> Set<Set<T>> sccs(Map<T, Set<T>> graph) {
        final Map<T, Integer> positions
            = new DepthFirstSearch<T>(graph, null).finished;
        final List<T> elements = new ArrayList<T>(positions.keySet());
        Collections.sort(elements, new CompareByPosition<T>(positions));
        Collections.reverse(elements);
        final Map<T, T> predecessor
            = new DepthFirstSearch<T>(reversed(graph), elements).predecessor;
        class Components {
            Map<T, Set<T>> map = new HashMap<T, Set<T>>();
            Set<T> component(T t) {
                Set<T> out = map.get(t);
                if (out == null) {
                    T pred = predecessor.get(t);
                    if (pred == null) {
                        out = new HashSet<T>();
                    } else {
                        out = component(pred);
                    }
                    out.add(t);
                    map.put(t, out);
                }
                return out;
            }
            Components() {
                for (T t : elements) {
                    component(t);
                }
            }
        }
        return new HashSet<Set<T>>(new Components().map.values());
    }
    
    /**
     * Check whether all edges of one graph are contained in another.
     */
    public static <T> boolean isSubgraphOf(Map<T, Set<T>> subGraph,
                                           Map<T, Set<T>> superGraph) {
        for (Map.Entry<T, Set<T>> e : subGraph.entrySet()) {
            if (!successors(e.getKey(), superGraph)
                    .containsAll(e.getValue())) {
                return false;
            }
        }
        return true;
    }
    
    public static <T> void restrictToDomain(Map<T, Set<T>> graph,
                                            Set<T> domain) {
        for (Iterator<Map.Entry<T, Set<T>>> i = graph.entrySet().iterator();
             i.hasNext(); ) {
            Map.Entry<T, Set<T>> e = i.next();
            if (domain.contains(e.getKey())) {
                e.getValue().retainAll(domain);
            } else {
                i.remove();
            }
        }
    }
    
    // public static void main(String[] args) {
    //     class Relation {
    //         public Map<Integer, Set<Integer>> map;
    //         public Relation() {
    //             map = new TreeMap<Integer, Set<Integer>>();
    //         }
    //         public void add(int node, int... successors) {
    //             Set<Integer> neighbors = map.get(new Integer(node));
    //             if (neighbors == null) {
    //                 neighbors = new TreeSet<Integer>();
    //                 map.put(new Integer(node), neighbors);
    //             }
    //             for (int i : successors) neighbors.add(new Integer(i));
    //         }
    //     }
    //     Relation r = new Relation();
    //     // r.add(0, 0);
    //     // r.add(1, 1);
    //     // r.add(2, 2);
    //     r.add(0, 1);
    //     // r.add(2, 1);
    //     r.add(1, 2);
    //     printGraph(r.map);
    //     System.out.println("reversed:");
    //     printGraph(reversed(r.map));
    //     for (Set<Integer> comp : sccs(r.map)) {
    //         System.out.println("component:");
    //         for (Integer i : comp) {
    //             System.out.println(i);
    //         }
    //     }
    //     Acyclic<Integer> acyc = new Acyclic<Integer>(r.map, false);
    //     System.out.println("acyclic:");
    //     printGraph(acyc.graph);
    //     List<Integer> sorted = topologicalSort(acyc.graph);
    //     for (Integer i : sorted) {
    //         System.out.println(i);
    //     }
    // }

}
