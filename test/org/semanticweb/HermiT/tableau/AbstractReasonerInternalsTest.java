package org.semanticweb.HermiT.tableau;

import java.util.Collections;
import java.util.HashMap;
import java.util.Set;

import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.blocking.AnywhereBlocking;
import org.semanticweb.HermiT.blocking.BlockingSignatureCache;
import org.semanticweb.HermiT.blocking.BlockingStrategy;
import org.semanticweb.HermiT.blocking.DirectBlockingChecker;
import org.semanticweb.HermiT.blocking.PairWiseDirectBlockingChecker;
import org.semanticweb.HermiT.existentials.CreationOrderStrategy;
import org.semanticweb.HermiT.existentials.ExpansionStrategy;
import org.semanticweb.HermiT.model.DLOntology;
import org.semanticweb.HermiT.model.DescriptionGraph;
import org.semanticweb.HermiT.monitor.TableauMonitor;
import org.semanticweb.HermiT.owlapi.structural.OWLClausification;
import org.semanticweb.HermiT.reasoner.AbstractReasonerTest;
import org.semanticweb.HermiT.tableau.ExtensionTable;
import org.semanticweb.HermiT.tableau.Tableau;

public class AbstractReasonerInternalsTest extends AbstractReasonerTest {

    public AbstractReasonerInternalsTest(String name) {
        super(name);
    }

    protected DLOntology getDLOntology(Configuration c,Set<DescriptionGraph> dgs) throws Exception {
        OWLClausification clausification=new OWLClausification(c);
        if (dgs==null)
            dgs=Collections.emptySet();
        return clausification.clausify(m_ontologyManager,m_ontology,dgs);
    }

    protected Tableau getTableau(Set<DescriptionGraph> dgs) throws Exception {
        Configuration c=new Configuration();
        c.directBlockingType=Configuration.DirectBlockingType.PAIR_WISE;
        c.blockingStrategyType=Configuration.BlockingStrategyType.ANYWHERE;
        c.existentialStrategyType=Configuration.ExistentialStrategyType.CREATION_ORDER;

        DLOntology dlOntology=getDLOntology(c,dgs);

        DirectBlockingChecker directBlockingChecker=PairWiseDirectBlockingChecker.INSTANCE;
        BlockingSignatureCache blockingSignatureCache=new BlockingSignatureCache(directBlockingChecker);
        BlockingStrategy blockingStrategy=new AnywhereBlocking(directBlockingChecker,blockingSignatureCache);
        ExpansionStrategy ExpansionStrategy=new CreationOrderStrategy(blockingStrategy);

        return new Tableau(getTableauMonitor(),ExpansionStrategy,dlOntology,new HashMap<String,Object>());
    }

    protected Tableau getTableau() throws Exception {
        return getTableau(null);
    }

    protected TableauMonitor getTableauMonitor() {
        return null;
    }

    protected boolean shouldPrepareForNIRule() {
        return false;
    }

    protected static void assertRetrieval(ExtensionTable extensionTable,Object[] searchTuple,ExtensionTable.View extensionView,Object[][] expectedTuples) {
        boolean[] bindingPattern=new boolean[searchTuple.length];
        for (int i=0;i<searchTuple.length;i++)
            if (searchTuple[i]!=null)
                bindingPattern[i]=true;
        ExtensionTable.Retrieval retrieval=extensionTable.createRetrieval(bindingPattern,extensionView);
        System.arraycopy(searchTuple,0,retrieval.getBindingsBuffer(),0,searchTuple.length);
        assertRetrieval(retrieval,expectedTuples);
    }

    protected static void assertRetrieval(ExtensionTable.Retrieval retrieval,Object[][] expectedTuples) {
        retrieval.open();
        boolean[] consumed=new boolean[expectedTuples.length];
        while (!retrieval.afterLast()) {
            Object[] tupleBuffer=retrieval.getTupleBuffer();
            boolean tupleFound=false;
            for (int i=0;!tupleFound&&i<expectedTuples.length;i++) {
                if (!consumed[i]&&tuplesEqual(tupleBuffer,expectedTuples[i])) {
                    consumed[i]=true;
                    tupleFound=true;
                }
            }
            if (!tupleFound)
                fail("Tuple from the retrieval not found in the expected tuples.");
            retrieval.next();
        }
        for (int i=0;i<consumed.length;i++)
            if (!consumed[i])
                fail("Tuple from the expected list has not been seen in the retrieval.");
    }

    protected static void assertEquals(Object[] tuple1,Object[] tuple2) {
        assertEquals(tuple1.length,tuple2.length);
        for (int index=0;index<tuple1.length;index++)
            assertEquals(tuple1[index],tuple2[index]);
    }

    protected static boolean tuplesEqual(Object[] tuple1,Object[] tuple2) {
        if (tuple1.length!=tuple2.length)
            return false;
        for (int i=0;i<tuple1.length;i++)
            if (!tuple1[i].equals(tuple2[i]))
                return false;
        return true;
    }

    protected static Object[] T(Object... nodes) {
        return nodes;
    }
}
