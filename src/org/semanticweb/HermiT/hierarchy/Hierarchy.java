// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.hierarchy;

public interface Hierarchy<T> {
    interface Element<T> {
        boolean doesPrecede(T other);
        boolean doesSucceed(T other);
        T getEquivalent(); // might just return null
    }
    HierarchyPosition<T> getPosition(Element<T> e);
}
