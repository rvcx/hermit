// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.blocking;

import java.io.Serializable;

import org.semanticweb.HermiT.model.*;
import org.semanticweb.HermiT.tableau.*;

public class AncestorBlocking implements BlockingStrategy,Serializable {
    private static final long serialVersionUID=1075850000309773283L;

    protected final DirectBlockingChecker m_directBlockingChecker;
    protected final BlockingSignatureCache m_blockingSignatureCache;
    protected Tableau m_tableau;

    public AncestorBlocking(DirectBlockingChecker directBlockingChecker,BlockingSignatureCache blockingSignatureCache) {
        m_directBlockingChecker=directBlockingChecker;
        m_blockingSignatureCache=blockingSignatureCache;
    }
    public void initialize(Tableau tableau) {
        m_tableau=tableau;
    }
    public void clear() {
    }
    public void computeBlocking() {
        Node node=m_tableau.getFirstTableauNode();
        while (node!=null) {
            if (node.isActive()) {
                Node parent=node.getParent();
                if (parent==null)
                    node.setBlocked(null,false);
                else if (parent.isBlocked())
                    node.setBlocked(parent,false);
                else if (m_blockingSignatureCache!=null) {
                    if (m_blockingSignatureCache.containsSignature(node))
                        node.setBlocked(Node.CACHE_BLOCKER,true);
                    else
                        checkParentBlocking(node);
                }
                else
                    checkParentBlocking(node);
            }
            node=node.getNextTableauNode();
        }
    }
    protected final void checkParentBlocking(Node node) {
        Node blocker=node.getParent();
        while (blocker!=null) {
            if (m_directBlockingChecker.isBlockedBy(blocker,node)) {
                node.setBlocked(blocker,true);
                break;
            }
            blocker=blocker.getParent();
        }
    }
    public void assertionAdded(Concept concept,Node node) {
    }
    public void assertionRemoved(Concept concept,Node node) {
    }
    public void assertionAdded(AtomicRole atomicRole,Node nodeFrom,Node nodeTo) {
    }
    public void assertionRemoved(AtomicRole atomicRole,Node nodeFrom,Node nodeTo) {
    }
    public void nodeStatusChanged(Node node) {
    }
    public void nodeDestroyed(Node node) {
    }
    public void modelFound() {
        if (m_blockingSignatureCache!=null) {
            computeBlocking();
            Node node=m_tableau.getFirstTableauNode();
            while (node!=null) {
                if (!node.isBlocked() && m_directBlockingChecker.canBeBlocker(node))
                    m_blockingSignatureCache.addNode(node);
                node=node.getNextTableauNode();
            }
        }
    }
}
