// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.hierarchy;

import java.util.Set;
import java.util.HashSet;
import java.util.Collections;

public class TaxonomyPosition<T> implements HierarchyPosition<T> {
    private Taxonomy<T> tax;
    private T vertex;
    TaxonomyPosition(Taxonomy<T> taxonomy, T element) {
        tax = taxonomy;
        vertex = taxonomy.canonical.get(element);
        assert vertex != null;
    }
    
    public Set<T> getEquivalents() {
        return Collections.unmodifiableSet(tax.equivs.get(vertex));
    }
    public Set<T> getAncestors() {
        Set<T> output = new HashSet<T>();
        for (T anc : tax.closed.get(vertex)) {
            output.addAll(tax.equivs.get(anc));
        }
        return output;
    }
    public Set<T> getDescendants() {
        Set<T> output = new HashSet<T>();
        for (T desc : tax.closed_inverse.get(vertex)) {
            output.addAll(tax.equivs.get(desc));
        }
        return output;
    }
    public Set<HierarchyPosition<T>> getParentPositions() {
        Set<HierarchyPosition<T>> output = new HashSet<HierarchyPosition<T>>();
        for (T parent : tax.reduced.get(vertex)) {
            output.add(new TaxonomyPosition<T>(tax, parent));
        }
        return output;
    }
    public Set<HierarchyPosition<T>> getChildPositions() {
        Set<HierarchyPosition<T>> output = new HashSet<HierarchyPosition<T>>();
        for (T child : tax.reduced_inverse.get(vertex)) {
            output.add(new TaxonomyPosition<T>(tax, child));
        }
        return output;
    }
    public Set<HierarchyPosition<T>> getAncestorPositions() {
        Set<HierarchyPosition<T>> output = new HashSet<HierarchyPosition<T>>();
        for (T parent : tax.closed.get(vertex)) {
            output.add(new TaxonomyPosition<T>(tax, parent));
        }
        return output;
    }
    public Set<HierarchyPosition<T>> getDescendantPositions() {
        Set<HierarchyPosition<T>> output = new HashSet<HierarchyPosition<T>>();
        for (T child : tax.closed_inverse.get(vertex)) {
            output.add(new TaxonomyPosition<T>(tax, child));
        }
        return output;
    }
    
    // These are created on demand, so compare values based on content and not
    // object identity:
    public int hashCode() {
        return tax.hashCode() ^ vertex.hashCode();
    }
    public boolean equals(Object other) {
        if (other instanceof TaxonomyPosition) {
            TaxonomyPosition otherPos = (TaxonomyPosition) other;
            return tax.equals(otherPos.tax) && vertex.equals(otherPos.vertex);
        } else return false;
    }
    
    public static class TransientPosition<T> implements HierarchyPosition<T> {
        Taxonomy<T> tax;
        Taxonomy<T>.Position pos;
        TransientPosition(Taxonomy<T> taxonomy,
                          Taxonomy<T>.Position position) {
            tax = taxonomy;
            pos = position;
        }
        public Set<T> getEquivalents() {
            return Collections.emptySet();
        }
        public Set<T> getAncestors() {
            Set<T> output = new HashSet<T>();
            for (T parent : pos.successors) {
                for (T anc : tax.closed.get(parent)) {
                    if (!output.contains(anc)) {
                        output.addAll(tax.equivs.get(anc));
                    }
                }
            }
            return output;
        }
        public Set<T> getDescendants() {
            Set<T> output = new HashSet<T>();
            for (T child : pos.predecessors) {
                for (T desc : tax.closed_inverse.get(child)) {
                    if (!output.contains(desc)) {
                        output.addAll(tax.equivs.get(desc));
                    }
                }
            }
            return output;
        }
        public Set<HierarchyPosition<T>> getParentPositions() {
            Set<HierarchyPosition<T>> output
                = new HashSet<HierarchyPosition<T>>();
            for (T parent : pos.successors) {
                output.add(new TaxonomyPosition<T>(tax, parent));
            }
            return output;
        }
        public Set<HierarchyPosition<T>> getChildPositions() {
            Set<HierarchyPosition<T>> output
                = new HashSet<HierarchyPosition<T>>();
            for (T parent : pos.successors) {
                output.add(new TaxonomyPosition<T>(tax, parent));
            }
            return output;
        }
        public Set<HierarchyPosition<T>> getAncestorPositions() {
            Set<HierarchyPosition<T>> output
                = new HashSet<HierarchyPosition<T>>();
            for (HierarchyPosition<T> pos : getParentPositions()) {
                output.addAll(pos.getAncestorPositions());
            }
            return output;
        }
        public Set<HierarchyPosition<T>> getDescendantPositions() {
            Set<HierarchyPosition<T>> output
                = new HashSet<HierarchyPosition<T>>();
            for (HierarchyPosition<T> pos : getChildPositions()) {
                output.addAll(pos.getDescendantPositions());
            }
            return output;
        }
    }

}
