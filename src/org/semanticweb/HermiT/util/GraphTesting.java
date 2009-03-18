// Copyright 2009 by Rob Shearer; see license.txt for details
package org.semanticweb.HermiT.util;

import java.util.Map;
import java.util.Set;
import java.io.PrintStream;
import java.util.TreeMap;
import java.util.HashMap;
import java.util.TreeSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Collection;
import java.util.ArrayList;

public class GraphTesting {
    public static <T> void printGraph(Map<T, Set<T>> graph,
                                      PrintStream stream) {
        for (Map.Entry<T, Set<T>> e : graph.entrySet()) {
            if (e.getValue().isEmpty()) {
                stream.print(e.getKey());
                stream.println(" no successors");
            }
            for (T t : e.getValue()) {
                stream.print(e.getKey());
                stream.print(" -> ");
                stream.println(t);
            }
        }
    }
    
    public static <T> void removeEdges(Map<T, Set<T>> graph,
                                       double fractionRemoved,
                                       java.util.Random rand) {
        for (Map.Entry<T, Set<T>> e : graph.entrySet()) {
            for (Iterator<T> i = e.getValue().iterator(); i.hasNext(); ) {
                i.next();
                if (rand.nextDouble() < fractionRemoved) i.remove();
            }
        }
    }
    
    public static <T> void addEdges(Map<T, Set<T>> graph,
                                    Collection<T> domain,
                                    int numToAdd,
                                    java.util.Random rand) {
        ArrayList<T> choices = new ArrayList<T>(domain);
        for (int i = 0; i < numToAdd; ++i) {
            GraphUtils.successorSet(choices.get(rand.nextInt(choices.size())), graph)
                .add(choices.get(rand.nextInt(choices.size())));
        }
    }
    
    public static <T> Map<T, Set<T>> cloneGraph(Map<T, Set<T>> original) {
        Map<T, Set<T>> out = new HashMap<T, Set<T>>();
        for (Map.Entry<T, Set<T>> e : original.entrySet()) {
            out.put(e.getKey(), new HashSet<T>(e.getValue()));
        }
        return out;
    }

    public static class IntegerGraph {
        public Map<Integer, Set<Integer>> graph
            = new TreeMap<Integer, Set<Integer>>();
        public void add(int node, int... successors) {
            Set<Integer> neighbors
                = GraphUtils.successorSet(new Integer(node), graph);
            for (int i : successors) neighbors.add(new Integer(i));
        }
    }
    
    public static class LadderGraph {
        public Set<Integer> domain = new HashSet<Integer>();
        public Map<Integer, Set<Integer>> graph;
        public LadderGraph(int rungs) {
            if (rungs < 1) rungs = 1;
            IntegerGraph igraph = new IntegerGraph();
            igraph.add(0, 1, 2);
            for (int i = 1; i < rungs; ++i) {
                igraph.add(i * 2 - 1, i * 2 + 1, i * 2 + 2);
                igraph.add(i * 2, i * 2 + 1, i * 2 + 2);
            }
            igraph.add(rungs * 2 - 1, rungs * 2 + 1);
            igraph.add(rungs * 2, rungs * 2 + 1);
            igraph.add(rungs * 2 + 1);
            for (int i = 0; i <= rungs * 2 + 1; ++i) {
                domain.add(new Integer(i));
            }
            graph = igraph.graph;
        }
    }

}
