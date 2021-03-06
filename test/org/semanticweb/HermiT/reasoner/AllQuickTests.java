package org.semanticweb.HermiT.reasoner;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class AllQuickTests extends TestCase {

    public static Test suite() {
        TestSuite suite = new TestSuite("Unit tests for HermiT as a blackbox.");
        // $JUnit-BEGIN$
        suite.addTestSuite(DatatypesTest.class);
        suite.addTestSuite(ReasonerTest.class);
        suite.addTestSuite(ReasonerIndividualReuseTest.class);
        suite.addTestSuite(ComplexConceptTest.class);
        // $JUnit-END$
        return suite;
    }
}
