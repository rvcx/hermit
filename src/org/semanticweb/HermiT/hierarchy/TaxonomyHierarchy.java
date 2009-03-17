// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.hierarchy;

public class TaxonomyHierarchy<T> implements Hierarchy<T> {
    private Taxonomy<T> tax;
    public TaxonomyHierarchy(Taxonomy<T> tax) {
        this.tax = tax;
    }
    public HierarchyPosition<T> getPosition(Element<T> e) {
        Taxonomy<T>.Position pos = tax.getPosition(e, null, null, null, null);
        if (pos.successors.equals(pos.predecessors)) {
            assert pos.successors.size() == 1;
            assert pos.predecessors.size() == 1;
            return new TaxonomyPosition<T>(tax, pos.successors.iterator().next());
        } else {
            return new TaxonomyPosition.TransientPosition<T>(tax, pos);
        }
    }
}
