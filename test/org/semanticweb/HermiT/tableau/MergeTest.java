package org.semanticweb.HermiT.tableau;

import java.util.Collections;
import java.util.Set;

import org.semanticweb.HermiT.blocking.*;
import org.semanticweb.HermiT.existentials.*;
import org.semanticweb.HermiT.model.*;

public class MergeTest extends AbstractHermiTTest {
    protected static final AtomicConcept A=AtomicConcept.create("A");
    protected static final AtomicConcept B=AtomicConcept.create("B");
    protected static final AtomicConcept C=AtomicConcept.create("C");
    protected static final AtomicConcept D=AtomicConcept.create("D");
    protected static final AtomicAbstractRole R=AtomicAbstractRole.create("R");
    protected static final AtomicNegationConcept NEG_A=AtomicNegationConcept.create(A);
    protected static final AtLeastAbstractRoleConcept EXISTS_NEG_A=AtLeastAbstractRoleConcept.create(1,R,NEG_A);
    protected static final DLOntology TEST_DL_ONTOLOGY;
    static {
        Variable X=Variable.create("X");
        Variable Y=Variable.create("Y");
        DLClause cl=DLClause.create(new Atom[][] { { Atom.create(EXISTS_NEG_A,X) } },new Atom[] { Atom.create(R,X,Y),Atom.create(A,Y) });
        Set<DLClause> dlClauses=Collections.singleton(cl);
        Set<Atom> atoms=Collections.emptySet();
        TEST_DL_ONTOLOGY=new DLOntology("opaque:test",dlClauses,atoms,atoms,false,false,false,false);
    }

    protected Tableau m_tableau;
    protected ExtensionManager m_extensionManager;

    public MergeTest(String name) {
        super(name);
    }
    protected void setUp() {
        BlockingCache blockingCache=new BlockingCache(PairWiseDirectBlockingChecker.INSTANCE);
        BlockingStrategy blockingStrategy=new AnywhereBlocking(PairWiseDirectBlockingChecker.INSTANCE,blockingCache);
        ExistentialsExpansionStrategy existentialsExpansionStrategy=new CreationOrderStrategy(blockingStrategy);
        m_tableau=new Tableau(null,existentialsExpansionStrategy,TEST_DL_ONTOLOGY);
        m_extensionManager=m_tableau.getExtensionManager();
    }
    public void testMergeAndBacktrack() {
        DependencySet emptySet=m_tableau.getDependencySetFactory().emptySet();
        Node a=m_tableau.createNewRootNode(emptySet,0);
        Node b=m_tableau.createNewRootNode(emptySet,0);
        Node a1=m_tableau.createNewTreeNode(a,emptySet);
        Node a2=m_tableau.createNewTreeNode(a,emptySet);
        Node a11=m_tableau.createNewTreeNode(a1,emptySet);
        Node a12=m_tableau.createNewTreeNode(a1,emptySet);

        m_extensionManager.addAssertion(R,a,a1,emptySet);
        m_extensionManager.addAssertion(R,a,a2,emptySet);
        
        m_extensionManager.addConceptAssertion(A,a1,emptySet);
        m_extensionManager.addConceptAssertion(EXISTS_NEG_A,a1,emptySet);

        m_extensionManager.addConceptAssertion(NEG_A,a2,emptySet);
        m_extensionManager.addConceptAssertion(B,a2,emptySet);
        m_extensionManager.addConceptAssertion(C,a2,emptySet);
        m_extensionManager.addConceptAssertion(D,a2,emptySet);

        m_extensionManager.addAssertion(R,a1,a11,emptySet);
        m_extensionManager.addAssertion(R,a1,a12,emptySet);

        m_extensionManager.addConceptAssertion(A,a11,emptySet);
        m_extensionManager.addConceptAssertion(A,a12,emptySet);

        m_extensionManager.addAssertion(R,a1,b,emptySet);

        BranchingPoint bp=new BranchingPoint(m_tableau);
        m_tableau.pushBranchingPoint(bp);
        
        // The label of a2 is larger, so a1 is merged into a2
        m_extensionManager.addAssertion(Equality.INSTANCE,a1,a2,emptySet);
        
        assertTrue(m_extensionManager.containsClash());
        assertContainsAll(a2.getPositiveLabel(),A,EXISTS_NEG_A,B,C,D);
        assertContainsAll(a2.getNegativeLabel(),A);
        
        assertTrue(a1.isMerged());
        assertSame(a1.getCanonicalNode(),a2);
        assertFalse(a11.isInTableau());
        assertFalse(a12.isInTableau());
        
        assertRetrieval(m_extensionManager.getTernaryExtensionTable(),T(R,null,null),ExtensionTable.View.TOTAL,new Object[][] { T(R,a,a2),T(R,a2,b) });
        assertRetrieval(m_extensionManager.getBinaryExtensionTable(),T(A,null),ExtensionTable.View.TOTAL,new Object[][] { T(A,a2) });

        
        m_tableau.backtrackTo(bp.getLevel());
        
        assertFalse(m_extensionManager.containsClash());
        assertContainsAll(a2.getPositiveLabel(),B,C,D);
        assertContainsAll(a2.getNegativeLabel(),A);

        assertFalse(a1.isMerged());
        assertSame(a1.getCanonicalNode(),a1);
        assertTrue(a11.isInTableau());
        assertTrue(a12.isInTableau());
        
        assertRetrieval(m_extensionManager.getTernaryExtensionTable(),T(R,null,null),ExtensionTable.View.TOTAL,new Object[][] { T(R,a,a1),T(R,a1,a11),T(R,a1,a12),T(R,a1,b),T(R,a,a2) });
        assertRetrieval(m_extensionManager.getBinaryExtensionTable(),T(A,null),ExtensionTable.View.TOTAL,new Object[][] { T(A,a1),T(A,a11),T(A,a12) });

        
        m_extensionManager.addAssertion(Inequality.INSTANCE,a11,a12,emptySet);
        assertRetrieval(m_extensionManager.getTernaryExtensionTable(),T(Inequality.INSTANCE,null,null),ExtensionTable.View.TOTAL,new Object[][] { T(Inequality.INSTANCE,a11,a12) });
        
        
        m_extensionManager.addAssertion(Equality.INSTANCE,a11,a12,emptySet);
        assertTrue(m_extensionManager.containsClash());
        
        
        m_tableau.backtrackTo(bp.getLevel());

        assertFalse(m_extensionManager.containsClash());
        assertRetrieval(m_extensionManager.getTernaryExtensionTable(),T(Inequality.INSTANCE,null,null),ExtensionTable.View.TOTAL,NO_TUPLES);
    }
}
