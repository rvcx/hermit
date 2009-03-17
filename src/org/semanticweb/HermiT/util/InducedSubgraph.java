// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.util;

import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;
import java.util.AbstractMap;

public class InducedSubgraph<T> extends AbstractMap<T, Set<T>> {
    private Map<T, Set<T>> graph;
    private Set<T> elements;
    private Map<T, Set<T>> cache = new HashMap<T, Set<T>>();
    private boolean keysCached = false;
    
    private void cacheKeys() {
        if (!keysCached) {
            for (T key : elements) {
                if (graph.containsKey(key)) {
                    cache.put(key, null);
                }
            }
        }
        keysCached = true;
    }
    
    public InducedSubgraph(Map<T, Set<T>> graph, Set<T> elements) {
        this.graph = graph;
        this.elements = elements;
    }
    
    public boolean containsKey(Object key) {
        return graph.containsKey(key) && elements.contains(key);
    }
    
    public Set<Map.Entry<T, Set<T>>> entrySet() {
        for (T key : this.keySet()) {
            this.get(key);
        }
        return cache.entrySet();
    }
    
    public Set<T> get(T key) {
        Set<T> out = cache.get(key);
        if (out == null && elements.contains(key)) {
            out = new HashSet<T>(graph.get(key));
            out.retainAll(elements);
            cache.put(key, out);
        }
        return out;
    }
    
    public boolean isEmpty() {
        cacheKeys(); // could check this more efficienty
        return cache.isEmpty();
    }
    
    public Set<T> keySet() {
        cacheKeys();
        return cache.keySet();
    }
    
    public int size() {
        cacheKeys();
        return cache.size();
    }
}