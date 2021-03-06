// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.tableau;

import java.io.Serializable;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.Concept;
import org.semanticweb.HermiT.model.DLPredicate;
import org.semanticweb.HermiT.model.DescriptionGraph;
import org.semanticweb.HermiT.model.Equality;
import org.semanticweb.HermiT.model.InverseRole;
import org.semanticweb.HermiT.model.Role;
import org.semanticweb.HermiT.monitor.TableauMonitor;

public final class ExtensionManager implements Serializable {
    private static final long serialVersionUID=5900300914631070591L;

    protected final Tableau m_tableau;
    protected final TableauMonitor m_tableauMonitor;
    protected final DependencySetFactory m_dependencySetFactory;
    protected final Map<Integer,ExtensionTable> m_extensionTablesByArity;
    protected final ExtensionTable[] m_allExtensionTablesArray;
    protected final ExtensionTable m_binaryExtensionTable;
    protected final ExtensionTable m_ternaryExtensionTable;
    protected final Object[] m_binaryAuxiliaryTupleContains;
    protected final Object[] m_binaryAuxiliaryTupleAdd;
    protected final Object[] m_ternaryAuxiliaryTupleContains;
    protected final Object[] m_ternaryAuxiliaryTupleAdd;
    protected final Map<DescriptionGraph,Object[]> m_descriptionGraphTuplesContains;
    protected final Map<DescriptionGraph,Object[]> m_descriptionGraphTuplesAdd;
    protected PermanentDependencySet m_clashDependencySet;
    protected boolean m_addActive;

    public ExtensionManager(Tableau tableau) {
        m_tableau=tableau;
        m_tableauMonitor=m_tableau.m_tableauMonitor;
        m_dependencySetFactory=m_tableau.m_dependencySetFactory;
        m_extensionTablesByArity=new HashMap<Integer,ExtensionTable>();
        m_binaryExtensionTable = new ExtensionTableWithTupleIndexes(
                m_tableau, this, 2, !m_tableau.isDeterministic(),
                new TupleIndex[] {
            new TupleIndex(new int[] { 1,0 }),
            new TupleIndex(new int[] { 0,1 })
        }) {
            private static final long serialVersionUID=1462821385000191875L;

            public boolean isTupleActive(Object[] tuple) {
                return ((Node)tuple[1]).isActive();
            }
            public boolean isTupleActive(int tupleIndex) {
                return ((Node)m_tupleTable.getTupleObject(tupleIndex,1)).isActive();
            }
        };
        m_extensionTablesByArity.put(new Integer(2),m_binaryExtensionTable);
        m_ternaryExtensionTable = new ExtensionTableWithTupleIndexes(
                m_tableau, this,3,!m_tableau.isDeterministic(),
                new TupleIndex[] {
            new TupleIndex(new int[] { 0,1,2 }),
            new TupleIndex(new int[] { 1,2,0 }),
            new TupleIndex(new int[] { 2,0,1 })
        }) {
            private static final long serialVersionUID=-731201626401421877L;

            public boolean isTupleActive(Object[] tuple) {
                return ((Node)tuple[1]).isActive() && ((Node)tuple[2]).isActive();
            }
            public boolean isTupleActive(int tupleIndex) {
                return ((Node)m_tupleTable.getTupleObject(tupleIndex,1)).isActive() 
                    && ((Node)m_tupleTable.getTupleObject(tupleIndex,2)).isActive();
            }
        };
        m_extensionTablesByArity.put(new Integer(3),m_ternaryExtensionTable);
        for (DescriptionGraph descriptionGraph : m_tableau.getDLOntology().getAllDescriptionGraphs()) {
            Integer arityInteger=new Integer(descriptionGraph.getNumberOfVertices()+1);
            if (!m_extensionTablesByArity.containsKey(arityInteger)) {
                m_extensionTablesByArity.put(
                        arityInteger, 
                        new ExtensionTableWithFullIndex(
                                m_tableau, this, 
                                descriptionGraph.getNumberOfVertices()+1,
                                !m_tableau.isDeterministic()
                         )
                );
            }
        }
        m_allExtensionTablesArray=new ExtensionTable[m_extensionTablesByArity.size()];
        m_extensionTablesByArity.values().toArray(m_allExtensionTablesArray);
        m_binaryAuxiliaryTupleContains=new Object[2];
        m_binaryAuxiliaryTupleAdd=new Object[2];
        m_ternaryAuxiliaryTupleContains=new Object[3];
        m_ternaryAuxiliaryTupleAdd=new Object[3];
        m_descriptionGraphTuplesContains=new HashMap<DescriptionGraph,Object[]>();
        m_descriptionGraphTuplesAdd=new HashMap<DescriptionGraph,Object[]>();
        for (DescriptionGraph descriptionGraph : m_tableau.getDLOntology().getAllDescriptionGraphs()) {
            m_descriptionGraphTuplesContains.put(descriptionGraph,new Object[descriptionGraph.getNumberOfVertices()+1]);
            m_descriptionGraphTuplesAdd.put(descriptionGraph,new Object[descriptionGraph.getNumberOfVertices()+1]);
        }
    }
    public void clear() {
        for (int index=m_allExtensionTablesArray.length-1;index>=0;--index)
            m_allExtensionTablesArray[index].clear();
        m_clashDependencySet=null;
    }
    public void branchingPointPushed() {
        for (int index=m_allExtensionTablesArray.length-1;index>=0;--index)
            m_allExtensionTablesArray[index].branchingPointPushed();
    }
    public void backtrack() {
        for (int index=m_allExtensionTablesArray.length-1;index>=0;--index)
            m_allExtensionTablesArray[index].backtrack();
    }
    public ExtensionTable getBinaryExtensionTable() {
        return m_binaryExtensionTable;
    }
    public ExtensionTable getTernaryExtensionTable() {
        return m_ternaryExtensionTable;
    }
    public ExtensionTable getExtensionTable(int arity) {
        switch (arity) {
        case 2:
            return m_binaryExtensionTable;
        case 3:
            return m_ternaryExtensionTable;
        default:
            return m_extensionTablesByArity.get(arity);
        }
    }
    public Collection<ExtensionTable> getExtensionTables() {
        return m_extensionTablesByArity.values();
    }
    public boolean propagateDeltaNew() {
        boolean hasChange=false;
        for (int index=0;index<m_allExtensionTablesArray.length;index++)
            if (m_allExtensionTablesArray[index].propagateDeltaNew())
                hasChange=true;
        return hasChange;
    }
    public void clearClash() {
        if (m_clashDependencySet!=null) {
            m_dependencySetFactory.removeUsage(m_clashDependencySet);
            m_clashDependencySet=null;
        }
    }
    public void setClash(DependencySet clashDependencySet) {
        if (m_clashDependencySet!=null)
            m_dependencySetFactory.removeUsage(m_clashDependencySet);
        m_clashDependencySet=m_dependencySetFactory.getPermanent(clashDependencySet);
        if (m_clashDependencySet!=null)
            m_dependencySetFactory.addUsage(m_clashDependencySet);
    }
    public DependencySet getClashDependencySet() {
        return m_clashDependencySet;
    }
    public boolean containsClash() {
        return m_clashDependencySet!=null;
    }
    public boolean containsConceptAssertion(Concept concept,Node node) {
        if (AtomicConcept.THING.equals(concept))
            return true;
        else {
            m_binaryAuxiliaryTupleContains[0]=concept;
            m_binaryAuxiliaryTupleContains[1]=node;
            return m_binaryExtensionTable.containsTuple(m_binaryAuxiliaryTupleContains);
        }
    }
    public boolean containsRoleAssertion(Role role,Node nodeFrom,Node nodeTo) {
        if (role instanceof AtomicRole) {
            m_ternaryAuxiliaryTupleContains[0]=role;
            m_ternaryAuxiliaryTupleContains[1]=nodeFrom;
            m_ternaryAuxiliaryTupleContains[2]=nodeTo;
        }
        else {
            m_ternaryAuxiliaryTupleContains[0]=((InverseRole)role).getInverseOf();
            m_ternaryAuxiliaryTupleContains[1]=nodeTo;
            m_ternaryAuxiliaryTupleContains[2]=nodeFrom;
        }
        return m_ternaryExtensionTable.containsTuple(m_ternaryAuxiliaryTupleContains);
    }
    public boolean containsAssertion(DLPredicate dlPredicate,Node node) {
        if (AtomicConcept.THING.equals(dlPredicate))
            return true;
        else {
            m_binaryAuxiliaryTupleContains[0]=dlPredicate;
            m_binaryAuxiliaryTupleContains[1]=node;
            return m_binaryExtensionTable.containsTuple(m_binaryAuxiliaryTupleContains);
        }
    }
    public boolean containsAssertion(DLPredicate dlPredicate,Node node0,Node node1) {
        if (Equality.INSTANCE.equals(dlPredicate))
            return node0==node1;
        else {
            m_ternaryAuxiliaryTupleContains[0]=dlPredicate;
            m_ternaryAuxiliaryTupleContains[1]=node0;
            m_ternaryAuxiliaryTupleContains[2]=node1;
            return m_ternaryExtensionTable.containsTuple(m_ternaryAuxiliaryTupleContains);
        }
    }
    public boolean containsAssertion(DLPredicate dlPredicate,Node[] nodes) {
        ExtensionTable extensionTable=getExtensionTable(dlPredicate.getArity()+1);
        Object[] auxiliaryTuple;
        switch (dlPredicate.getArity()) {
        case 2:
            auxiliaryTuple=m_binaryAuxiliaryTupleContains;
            break;
        case 3:
            auxiliaryTuple=m_ternaryAuxiliaryTupleContains;
            break;
        default:
            auxiliaryTuple=m_descriptionGraphTuplesContains.get((DescriptionGraph)dlPredicate);
            break;
        }
        auxiliaryTuple[0]=dlPredicate;
        System.arraycopy(nodes,0,auxiliaryTuple,1,dlPredicate.getArity());
        return extensionTable.containsTuple(auxiliaryTuple);
    }
    public boolean containsTuple(Object[] tuple) {
        if (tuple.length==0)
            return containsClash();
        else
            return getExtensionTable(tuple.length).containsTuple(tuple);
    }
    public DependencySet getConceptAssertionDependencySet(Concept concept,Node node) {
        if (AtomicConcept.THING.equals(concept))
            return m_dependencySetFactory.emptySet();
        else {
            m_binaryAuxiliaryTupleContains[0]=concept;
            m_binaryAuxiliaryTupleContains[1]=node;
            return m_binaryExtensionTable.getDependencySet(m_binaryAuxiliaryTupleContains);
        }
    }
    public DependencySet getRoleAssertionDependencySet(Role role,Node nodeFrom,Node nodeTo) {
        if (role instanceof AtomicRole) {
            m_ternaryAuxiliaryTupleContains[0]=role;
            m_ternaryAuxiliaryTupleContains[1]=nodeFrom;
            m_ternaryAuxiliaryTupleContains[2]=nodeTo;
        }
        else {
            m_ternaryAuxiliaryTupleContains[0]=((InverseRole)role).getInverseOf();
            m_ternaryAuxiliaryTupleContains[1]=nodeTo;
            m_ternaryAuxiliaryTupleContains[2]=nodeFrom;
        }
        return m_ternaryExtensionTable.getDependencySet(m_ternaryAuxiliaryTupleContains);
    }
    public DependencySet getAssertionDependencySet(DLPredicate dlPredicate,Node node) {
        m_binaryAuxiliaryTupleContains[0]=dlPredicate;
        m_binaryAuxiliaryTupleContains[1]=node;
        return m_binaryExtensionTable.getDependencySet(m_binaryAuxiliaryTupleContains);
    }
    public DependencySet getAssertionDependencySet(DLPredicate dlPredicate,Node node0,Node node1) {
        if (Equality.INSTANCE.equals(dlPredicate))
            return node0==node1 ? m_dependencySetFactory.emptySet() : null;
        else {
            m_ternaryAuxiliaryTupleContains[0]=dlPredicate;
            m_ternaryAuxiliaryTupleContains[1]=node0;
            m_ternaryAuxiliaryTupleContains[2]=node1;
            return m_ternaryExtensionTable.getDependencySet(m_ternaryAuxiliaryTupleContains);
        }
    }
    public DependencySet getAssertionDependencySet(DLPredicate dlPredicate,Node[] nodes) {
        if (Equality.INSTANCE.equals(dlPredicate))
            return nodes[0]==nodes[1] ? m_dependencySetFactory.emptySet() : null;
        else if (AtomicConcept.THING.equals(dlPredicate))
            return m_dependencySetFactory.emptySet();
        else {
            ExtensionTable extensionTable=getExtensionTable(dlPredicate.getArity()+1);
            Object[] auxiliaryTuple;
            switch (dlPredicate.getArity()) {
            case 2:
                auxiliaryTuple=m_binaryAuxiliaryTupleContains;
                break;
            case 3:
                auxiliaryTuple=m_ternaryAuxiliaryTupleContains;
                break;
            default:
                auxiliaryTuple=m_descriptionGraphTuplesContains.get((DescriptionGraph)dlPredicate);
                break;
            }
            auxiliaryTuple[0]=dlPredicate;
            System.arraycopy(nodes,0,auxiliaryTuple,1,dlPredicate.getArity());
            return extensionTable.getDependencySet(auxiliaryTuple);
        }
    }
    public DependencySet getTupleDependencySet(Object[] tuple) {
        if (tuple.length==0)
            return m_clashDependencySet;
        else
            return getExtensionTable(tuple.length).getDependencySet(tuple);
    }
    public boolean addConceptAssertion(Concept concept,Node node,DependencySet dependencySet) {
        if (m_addActive)
            throw new IllegalStateException("ExtensionManager is not reentrant.");
        m_addActive=true;
        try {
            m_binaryAuxiliaryTupleAdd[0]=concept;
            m_binaryAuxiliaryTupleAdd[1]=node;
            return m_binaryExtensionTable.addTuple(m_binaryAuxiliaryTupleAdd,dependencySet);
        }
        finally {
            m_addActive=false;
        }
    }
    public boolean addRoleAssertion(Role role,Node nodeFrom,Node nodeTo,DependencySet dependencySet) {
        if (role instanceof AtomicRole)
            return addAssertion((AtomicRole)role,nodeFrom,nodeTo,dependencySet);
        else
            return addAssertion(((InverseRole)role).getInverseOf(),nodeTo,nodeFrom,dependencySet);
    }
    public boolean addAssertion(DLPredicate dlPredicate,Node node,DependencySet dependencySet) {
        if (m_addActive)
            throw new IllegalStateException("ExtensionManager is not reentrant.");
        m_addActive=true;
        try {
            m_binaryAuxiliaryTupleAdd[0]=dlPredicate;
            m_binaryAuxiliaryTupleAdd[1]=node;
            return m_binaryExtensionTable.addTuple(m_binaryAuxiliaryTupleAdd,dependencySet);
        }
        finally {
            m_addActive=false;
        }
    }
    public boolean addAssertion(DLPredicate dlPredicate,Node node0,Node node1,DependencySet dependencySet) {
        if (Equality.INSTANCE.equals(dlPredicate))
            return m_tableau.m_mergingManager.mergeNodes(node0,node1,dependencySet);
        else {
            if (m_addActive)
                throw new IllegalStateException("ExtensionManager is not reentrant.");
            m_addActive=true;
            try {
                m_ternaryAuxiliaryTupleAdd[0]=dlPredicate;
                m_ternaryAuxiliaryTupleAdd[1]=node0;
                m_ternaryAuxiliaryTupleAdd[2]=node1;
                return m_ternaryExtensionTable.addTuple(m_ternaryAuxiliaryTupleAdd,dependencySet);
            }
            finally {
                m_addActive=false;
            }
        }
    }
    public boolean addAssertion(DLPredicate dlPredicate,Node[] nodes,DependencySet dependencySet) {
        if (Equality.INSTANCE.equals(dlPredicate))
            return m_tableau.m_mergingManager.mergeNodes(nodes[0],nodes[1],dependencySet);
        else {
            if (m_addActive)
                throw new IllegalStateException("ExtensionManager is not reentrant.");
            m_addActive=true;
            try {
                ExtensionTable extensionTable=getExtensionTable(dlPredicate.getArity()+1);
                Object[] auxiliaryTuple;
                switch (dlPredicate.getArity()) {
                case 2:
                    auxiliaryTuple=m_binaryAuxiliaryTupleAdd;
                    break;
                case 3:
                    auxiliaryTuple=m_ternaryAuxiliaryTupleAdd;
                    break;
                default:
                    auxiliaryTuple=m_descriptionGraphTuplesAdd.get((DescriptionGraph)dlPredicate);
                    break;
                }
                auxiliaryTuple[0]=dlPredicate;
                System.arraycopy(nodes,0,auxiliaryTuple,1,dlPredicate.getArity());
                return extensionTable.addTuple(auxiliaryTuple,dependencySet);
            }
            finally {
                m_addActive=false;
            }
        }
    }
    public boolean addTuple(Object[] tuple,DependencySet dependencySet) {
        if (tuple.length==0) {
            boolean result=(m_clashDependencySet==null);
            setClash(dependencySet);
            return result;
        }
        else if (Equality.INSTANCE.equals(tuple[0]))
            return m_tableau.m_mergingManager.mergeNodes((Node)tuple[1],(Node)tuple[2],dependencySet);
        else {
            if (m_addActive)
                throw new IllegalStateException("ExtensionManager is not reentrant.");
            m_addActive=true;
            try {
                return getExtensionTable(tuple.length).addTuple(tuple,dependencySet); 
            }
            finally {
                m_addActive=false;
            }
        }
    }
}
