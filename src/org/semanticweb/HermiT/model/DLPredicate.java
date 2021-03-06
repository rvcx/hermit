// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.model;

import org.semanticweb.HermiT.Namespaces;

/**
 * Represents a DL predicate.
 */
public interface DLPredicate {
    /**
     * @return the arity of the predicate
     */
    int getArity();
    String toString(Namespaces namespaces);
}
