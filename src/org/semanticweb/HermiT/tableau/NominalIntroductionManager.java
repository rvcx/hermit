// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.tableau;

import java.io.Serializable;

import org.semanticweb.HermiT.model.AtMostGuard;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.Concept;
import org.semanticweb.HermiT.model.InverseRole;
import org.semanticweb.HermiT.model.Role;

/**
 * Implements the nominal introduction rule.
 */
public final class NominalIntroductionManager implements Serializable {
    private static final long serialVersionUID=5863617010809297861L;

    protected static final int ROOT_NODE=0;
    protected static final int TREE_NODE=1;
    protected static final int AT_MOST_CONCEPT=2;
    
    protected final Tableau m_tableau;
    protected final ExtensionManager m_extensionManager;
    protected final MergingManager m_mergingManager;
    protected final TupleTable m_targets;
    protected final Object[] m_bufferForTarget;
    protected final TupleTable m_newRootNodesTable;
    protected final TupleTableFullIndex m_newRootNodesIndex;
    protected final Object[] m_bufferForRootNodes;
    protected final ExtensionTable.Retrieval m_binaryExtensionTableSearch1Bound;
    protected final ExtensionTable.Retrieval m_ternaryExtensionTableSearch1Bound;
    protected final ExtensionTable.Retrieval m_ternaryExtensionTableSearch2Bound;
    protected final ExtensionTable.Retrieval m_ternaryExtensionTableSearch01Bound;
    protected final ExtensionTable.Retrieval m_ternaryExtensionTableSearch02Bound;
    protected int[] m_indicesByBranchingPoint;
    protected int m_firstUnprocessedTarget;
    
    public NominalIntroductionManager(Tableau tableau) {
        m_tableau=tableau;
        m_extensionManager=m_tableau.getExtensionManager();
        m_mergingManager=m_tableau.getMergingManager();
        m_targets=new TupleTable(3);
        m_bufferForTarget=new Object[3];
        m_newRootNodesTable=new TupleTable(4);
        m_newRootNodesIndex=new TupleTableFullIndex(m_newRootNodesTable,3);
        m_bufferForRootNodes=new Object[4];
        m_binaryExtensionTableSearch1Bound=m_extensionManager.m_binaryExtensionTable.createRetrieval(new boolean[] { false,true },ExtensionTable.View.TOTAL);
        m_ternaryExtensionTableSearch1Bound=m_extensionManager.m_ternaryExtensionTable.createRetrieval(new boolean[] { false,true,false },ExtensionTable.View.TOTAL);
        m_ternaryExtensionTableSearch2Bound=m_extensionManager.m_ternaryExtensionTable.createRetrieval(new boolean[] { false,false,true },ExtensionTable.View.TOTAL);
        m_ternaryExtensionTableSearch01Bound=m_extensionManager.m_ternaryExtensionTable.createRetrieval(new boolean[] { true,true,false },ExtensionTable.View.TOTAL);
        m_ternaryExtensionTableSearch02Bound=m_extensionManager.m_ternaryExtensionTable.createRetrieval(new boolean[] { true,false,true },ExtensionTable.View.TOTAL);
        m_indicesByBranchingPoint=new int[10*2];
        m_firstUnprocessedTarget=0;
    }
    public void clear() {
        m_targets.clear();
        for (int index=m_bufferForTarget.length-1;index>=0;--index)
            m_bufferForTarget[index]=null;
        m_newRootNodesTable.clear();
        m_newRootNodesIndex.clear();
        for (int index=m_bufferForRootNodes.length-1;index>=0;--index)
            m_bufferForRootNodes[index]=null;
        m_firstUnprocessedTarget=0;
    }
    public void branchingPointPushed() {
        int start=m_tableau.getCurrentBranchingPoint().getLevel()*3;
        int requiredSize=start+3;
        if (requiredSize>m_indicesByBranchingPoint.length) {
            int newSize=m_indicesByBranchingPoint.length*3/2;
            while (requiredSize>newSize)
                newSize=newSize*3/2;
            int[] newIndicesByBranchingPoint=new int[newSize];
            System.arraycopy(m_indicesByBranchingPoint,0,newIndicesByBranchingPoint,0,m_indicesByBranchingPoint.length);
            m_indicesByBranchingPoint=newIndicesByBranchingPoint;
        }
        m_indicesByBranchingPoint[start]=m_firstUnprocessedTarget;
        m_indicesByBranchingPoint[start+1]=m_targets.getFirstFreeTupleIndex();
        m_indicesByBranchingPoint[start+2]=m_newRootNodesTable.getFirstFreeTupleIndex();
    }
    public void backtrack() {
        int start=m_tableau.getCurrentBranchingPoint().getLevel()*3;
        m_firstUnprocessedTarget=m_indicesByBranchingPoint[start];
        m_targets.truncate(m_indicesByBranchingPoint[start+1]);
        int firstFreeNewRootNodeShouldBe=m_indicesByBranchingPoint[start+2];
        for (int tupleIndex=m_newRootNodesTable.getFirstFreeTupleIndex()-1;tupleIndex>=firstFreeNewRootNodeShouldBe;--tupleIndex)
            m_newRootNodesIndex.removeTuple(tupleIndex);
        m_newRootNodesTable.truncate(firstFreeNewRootNodeShouldBe);
    }
    public boolean processTargets() {
        boolean result=false;
        while (m_firstUnprocessedTarget<m_targets.getFirstFreeTupleIndex()) {
            m_targets.retrieveTuple(m_bufferForTarget,m_firstUnprocessedTarget);
            Node rootNode=(Node)m_bufferForTarget[ROOT_NODE];
            Node treeNode=(Node)m_bufferForTarget[TREE_NODE];
            m_firstUnprocessedTarget++;
            if (rootNode.isActive() && treeNode.isActive()) {
                AtMostGuard atMostRoleGuard=(AtMostGuard)m_bufferForTarget[AT_MOST_CONCEPT];
                if (m_tableau.m_tableauMonitor!=null)
                    m_tableau.m_tableauMonitor.nominalIntorductionStarted(rootNode,treeNode,atMostRoleGuard);
                DependencySet dependencySet=m_extensionManager.getConceptAssertionDependencySet(atMostRoleGuard,rootNode);
                dependencySet=m_tableau.getDependencySetFactory().unionWith(dependencySet,m_extensionManager.getRoleAssertionDependencySet(atMostRoleGuard.getOnRole(),rootNode,treeNode));
                if (!AtomicConcept.THING.equals(atMostRoleGuard.getToAtomicConcept()))
                    dependencySet=m_tableau.getDependencySetFactory().unionWith(dependencySet,m_extensionManager.getConceptAssertionDependencySet(atMostRoleGuard.getToAtomicConcept(),treeNode));
                if (atMostRoleGuard.getCaridnality()>1) {
                    BranchingPoint branchingPoint=new NominalIntroductionBranchingPoint(m_tableau,rootNode,treeNode,atMostRoleGuard);
                    m_tableau.pushBranchingPoint(branchingPoint);
                    dependencySet=m_tableau.getDependencySetFactory().addBranchingPoint(dependencySet,branchingPoint.getLevel());
                }
                Node newRootNode=getRootNodeFor(dependencySet,rootNode,atMostRoleGuard,1);
                if (!newRootNode.isActive()) {
                    assert newRootNode.isMerged();
                    dependencySet=newRootNode.addCacnonicalNodeDependencySet(dependencySet);
                    newRootNode=newRootNode.getCanonicalNode();
                }
                m_mergingManager.mergeNodes(treeNode,newRootNode,dependencySet);
                if (m_tableau.m_tableauMonitor!=null)
                    m_tableau.m_tableauMonitor.nominalIntorductionFinished(rootNode,treeNode,atMostRoleGuard);
                result=true;
            }
        }
        return result;
    }
    protected Node getRootNodeFor(DependencySet dependencySet,Node rootNode,AtMostGuard atMostRoleGuard,int number) {
        m_bufferForRootNodes[0]=rootNode;
        m_bufferForRootNodes[1]=atMostRoleGuard;
        m_bufferForRootNodes[2]=number;
        int tupleIndex=m_newRootNodesIndex.getTupleIndex(m_bufferForRootNodes);
        if (tupleIndex==-1) {
            Node newRootNode=m_tableau.createNewRootNode(dependencySet);
            m_bufferForRootNodes[3]=newRootNode;
            m_newRootNodesIndex.addTuple(m_bufferForRootNodes,m_newRootNodesTable.getFirstFreeTupleIndex());
            m_newRootNodesTable.addTuple(m_bufferForRootNodes);
            return newRootNode;
        }
        else
            return (Node)m_newRootNodesTable.getTupleObject(tupleIndex,3);
    }
    public void addNonnegativeConceptAssertion(Concept concept,Node node) {
        if ((node.getNodeType()==NodeType.NAMED_NODE || node.getNodeType()==NodeType.ROOT_NODE) 
                && concept instanceof AtMostGuard) {
            AtMostGuard atMost=(AtMostGuard)concept;
            Role onRole=atMost.getOnRole();
            AtomicConcept toAtomicConcept=atMost.getToAtomicConcept();
            if (onRole instanceof AtomicRole && node.m_numberOfNIAssertionsFromNode>0) {
                m_ternaryExtensionTableSearch01Bound.getBindingsBuffer()[0]=onRole;
                m_ternaryExtensionTableSearch01Bound.getBindingsBuffer()[1]=node;
                m_ternaryExtensionTableSearch01Bound.open();
                while (!m_ternaryExtensionTableSearch01Bound.afterLast()) {
                    Node treeNode=(Node)m_ternaryExtensionTableSearch01Bound.getTupleBuffer()[2];
                    if (treeNode.getNodeType()==NodeType.TREE_NODE 
                            && !node.isParentOf(treeNode) 
                            && (AtomicConcept.THING.equals(toAtomicConcept) 
                                    || m_extensionManager.containsAssertion(toAtomicConcept,treeNode)))
                        addTarget(node,treeNode,atMost);
                    m_ternaryExtensionTableSearch01Bound.next();
                }
            }
            else if (onRole instanceof InverseRole && node.m_numberOfNIAssertionsToNode>0) {
                m_ternaryExtensionTableSearch02Bound.getBindingsBuffer()[0]=((InverseRole)onRole).getInverseOf();
                m_ternaryExtensionTableSearch02Bound.getBindingsBuffer()[2]=node;
                m_ternaryExtensionTableSearch02Bound.open();
                while (!m_ternaryExtensionTableSearch02Bound.afterLast()) {
                    Node treeNode=(Node)m_ternaryExtensionTableSearch02Bound.getTupleBuffer()[1];
                    if (treeNode.getNodeType()==NodeType.TREE_NODE && !node.isParentOf(treeNode) && (AtomicConcept.THING.equals(toAtomicConcept) || m_extensionManager.containsAssertion(toAtomicConcept,treeNode)))
                        addTarget(node,treeNode,atMost);
                    m_ternaryExtensionTableSearch02Bound.next();
                }
            }
        }
        else if (node.getNodeType()==NodeType.TREE_NODE && concept instanceof AtomicConcept) {
            if (node.m_numberOfNIAssertionsFromNode>0) {
                m_ternaryExtensionTableSearch1Bound.getBindingsBuffer()[1]=node;
                m_ternaryExtensionTableSearch1Bound.open();
                while (!m_ternaryExtensionTableSearch1Bound.afterLast()) {
                    Node rootNode=(Node)m_ternaryExtensionTableSearch1Bound.getTupleBuffer()[2];
                    if ((rootNode.getNodeType()==NodeType.NAMED_NODE 
                            || rootNode.getNodeType()==NodeType.ROOT_NODE) 
                            && !rootNode.isParentOf(node)) {
                        Object atomicRole=m_ternaryExtensionTableSearch1Bound.getTupleBuffer()[0];
                        if (atomicRole instanceof AtomicRole) {
                            m_binaryExtensionTableSearch1Bound.getBindingsBuffer()[1]=rootNode;
                            m_binaryExtensionTableSearch1Bound.open();
                            while (!m_binaryExtensionTableSearch1Bound.afterLast()) {
                                Object rootNodeConcept=m_binaryExtensionTableSearch1Bound.getTupleBuffer()[0];
                                if (rootNodeConcept instanceof AtMostGuard) {
                                    AtMostGuard atMost=(AtMostGuard)rootNodeConcept;
                                    if (atMost.getOnRole() instanceof InverseRole && ((InverseRole)atMost.getOnRole()).getInverseOf().equals(atomicRole))
                                        addTarget(rootNode,node,atMost);
                                }
                                m_binaryExtensionTableSearch1Bound.next();
                            }
                        }
                    }
                    m_ternaryExtensionTableSearch1Bound.next();
                }
            }
            if (node.m_numberOfNIAssertionsToNode>0) {
                m_ternaryExtensionTableSearch2Bound.getBindingsBuffer()[2]=node;
                m_ternaryExtensionTableSearch2Bound.open();
                while (!m_ternaryExtensionTableSearch2Bound.afterLast()) {
                    Node rootNode=(Node)m_ternaryExtensionTableSearch2Bound.getTupleBuffer()[1];
                    if ((rootNode.getNodeType()==NodeType.NAMED_NODE 
                            || rootNode.getNodeType()==NodeType.ROOT_NODE) 
                            && !rootNode.isParentOf(node)) {
                        Object atomicRole=m_ternaryExtensionTableSearch2Bound.getTupleBuffer()[0];
                        if (atomicRole instanceof AtomicRole) {
                            m_binaryExtensionTableSearch1Bound.getBindingsBuffer()[1]=rootNode;
                            m_binaryExtensionTableSearch1Bound.open();
                            while (!m_binaryExtensionTableSearch1Bound.afterLast()) {
                                Object rootNodeConcept=m_binaryExtensionTableSearch1Bound.getTupleBuffer()[0];
                                if (rootNodeConcept instanceof AtMostGuard) {
                                    AtMostGuard atMost=(AtMostGuard)rootNodeConcept;
                                    if (atMost.getOnRole().equals(atomicRole))
                                        addTarget(rootNode,node,atMost);
                                }
                                m_binaryExtensionTableSearch1Bound.next();
                            }
                        }
                    }
                    m_ternaryExtensionTableSearch2Bound.next();
                }
            }
        }
    }
    public void addAtomicRoleAssertion(AtomicRole atomicRole,Node nodeFrom,Node nodeTo) {
        if ((nodeFrom.getNodeType()==NodeType.NAMED_NODE || nodeFrom.getNodeType()==NodeType.ROOT_NODE) 
                && nodeTo.getNodeType()==NodeType.TREE_NODE && !nodeFrom.isParentOf(nodeTo)) {
            nodeFrom.m_numberOfNIAssertionsFromNode++;
            nodeTo.m_numberOfNIAssertionsToNode++;
            m_binaryExtensionTableSearch1Bound.getBindingsBuffer()[1]=nodeFrom;
            m_binaryExtensionTableSearch1Bound.open();
            while (!m_binaryExtensionTableSearch1Bound.afterLast()) {
                Object concept=m_binaryExtensionTableSearch1Bound.getTupleBuffer()[0];
                if (concept instanceof AtMostGuard) {
                    AtMostGuard atMost=(AtMostGuard)concept;
                    if (atMost.getOnRole().equals(atomicRole)) {
                        AtomicConcept toAtomicConcept=atMost.getToAtomicConcept();
                        if (AtomicConcept.THING.equals(toAtomicConcept) 
                                || m_extensionManager.containsAssertion(toAtomicConcept,nodeTo))
                            addTarget(nodeFrom,nodeTo,atMost);
                    }
                }
                m_binaryExtensionTableSearch1Bound.next();
            }
        }
        else if (nodeFrom.getNodeType()==NodeType.TREE_NODE 
                && (nodeTo.getNodeType()==NodeType.NAMED_NODE || nodeTo.getNodeType()==NodeType.ROOT_NODE) 
                && !nodeTo.isParentOf(nodeFrom)) {
            nodeFrom.m_numberOfNIAssertionsFromNode++;
            nodeTo.m_numberOfNIAssertionsToNode++;
            m_binaryExtensionTableSearch1Bound.getBindingsBuffer()[1]=nodeTo;
            m_binaryExtensionTableSearch1Bound.open();
            while (!m_binaryExtensionTableSearch1Bound.afterLast()) {
                Object concept=m_binaryExtensionTableSearch1Bound.getTupleBuffer()[0];
                if (concept instanceof AtMostGuard) {
                    AtMostGuard atMost=(AtMostGuard)concept;
                    if (atMost.getOnRole() instanceof InverseRole 
                            && ((InverseRole)atMost.getOnRole()).getInverseOf().equals(atomicRole)) {
                        AtomicConcept toAtomicConcept=atMost.getToAtomicConcept();
                        if (AtomicConcept.THING.equals(toAtomicConcept) 
                                || m_extensionManager.containsAssertion(toAtomicConcept,nodeFrom))
                            addTarget(nodeTo,nodeFrom,atMost);
                    }
                }
                m_binaryExtensionTableSearch1Bound.next();
            }
        }
    }
    public void removeAtomicRoleAssertion(AtomicRole atomicRole,Node nodeFrom,Node nodeTo) {
        if (((nodeFrom.getNodeType()==NodeType.NAMED_NODE || nodeFrom.getNodeType()==NodeType.ROOT_NODE) 
                        && nodeTo.getNodeType()==NodeType.TREE_NODE 
                        && !nodeFrom.isParentOf(nodeTo)) 
                || ((nodeTo.getNodeType()==NodeType.NAMED_NODE || nodeTo.getNodeType()==NodeType.ROOT_NODE) 
                        &&  nodeFrom.getNodeType()==NodeType.TREE_NODE
                        && !nodeTo.isParentOf(nodeFrom))) {
            nodeFrom.m_numberOfNIAssertionsFromNode--;
            nodeTo.m_numberOfNIAssertionsToNode--;
        }
    }
    protected void addTarget(Node rootNode,Node treeNode,AtMostGuard atMost) {
        m_bufferForTarget[ROOT_NODE]=rootNode;
        m_bufferForTarget[TREE_NODE]=treeNode;
        m_bufferForTarget[AT_MOST_CONCEPT]=atMost;
        m_targets.addTuple(m_bufferForTarget);
    }
    
    protected class NominalIntroductionBranchingPoint extends BranchingPoint {
        private static final long serialVersionUID=6678113479704184263L;

        protected final Node m_rootNode;
        protected final Node m_treeNode;
        protected final AtMostGuard m_atMostRoleGuard;
        protected int m_currentRootNode;
        
        public NominalIntroductionBranchingPoint(Tableau tableau,Node rootNode,Node treeNode,AtMostGuard atMostRoleGuard) {
            super(tableau);
            m_rootNode=rootNode;
            m_treeNode=treeNode;
            m_atMostRoleGuard=atMostRoleGuard;
            m_currentRootNode=1; // This reflects the assumption that the first merge is performed from the NominalIntroductionManager
        }
        public void startNextChoice(Tableau tableau,DependencySet clashDepdendencySet) {
            m_currentRootNode++;
            assert m_currentRootNode<=m_atMostRoleGuard.getCaridnality();
            DependencySet dependencySet=clashDepdendencySet;
            if (m_currentRootNode==m_atMostRoleGuard.getCaridnality())
                dependencySet=tableau.getDependencySetFactory().removeBranchingPoint(dependencySet,m_level);
            Node newRootNode=getRootNodeFor(dependencySet,m_rootNode,m_atMostRoleGuard,m_currentRootNode);
            if (!newRootNode.isActive()) {
                assert newRootNode.isMerged();
                dependencySet=newRootNode.addCacnonicalNodeDependencySet(dependencySet);
                newRootNode=newRootNode.getCanonicalNode();
            }
            m_tableau.m_mergingManager.mergeNodes(m_treeNode,newRootNode,dependencySet);
        }
    }
}
