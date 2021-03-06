// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.model;

import java.io.Serializable;

import org.semanticweb.HermiT.*;

/**
 * Represents the inequality predicate.
 */
public class Inequality implements DLPredicate,Serializable {
    private static final long serialVersionUID=296924110684230279L;

    public static final Inequality INSTANCE=new Inequality();
    
    protected Inequality () {
    }
    public int getArity() {
        return 2;
    }
    public String toString(Namespaces namespaces) {
        return "!=";
    }
    public String toString() {
        return toString(Namespaces.none);
    }
    protected Object readResolve() {
        return INSTANCE;
    }
    public static Inequality create() {
        return INSTANCE;
    }
}
