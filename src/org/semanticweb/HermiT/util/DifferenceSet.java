// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.util;

import java.util.Set;
import java.util.AbstractSet;
import java.util.Collection;
import java.util.Iterator;
import java.util.HashSet;
import java.util.Collections;

public class DifferenceSet<T> extends AbstractSet<T> {
    private Set<? extends T> baseSet; // unmodifiable
    private Set<T> added = new HashSet<T>();
    private Set<T> removed = new HashSet<T>();
    
    public Iterator<T> iterator() {
        return new Iterator<T>() {
            int baseRemaining = baseSet.size() - removed.size();
            Iterator<? extends T> i = baseSet.iterator();
            T last = null;
        
            public boolean hasNext() {
                return baseRemaining > 0 || i.hasNext();
            }
            public T next() {
                last = i.next();
                if (--baseRemaining == 0) {
                    i = added.iterator();
                }
                return last;
            }
        
            public void remove() {
                if (baseRemaining >= 0) {
                    removed.add(last);
                } else {
                    i.remove();
                }
            }
        };
    }
    
    private boolean invariantsSatisfied() {
        for (T t : added) {
            if (baseSet.contains(t)) return false;
        }
        return baseSet.containsAll(removed);
    }
    
    public DifferenceSet(Set<? extends T> base) {
        baseSet = Collections.unmodifiableSet(base);
    }
    
    public boolean add(T t) {
        assert invariantsSatisfied();
        if (removed.remove(t)) return true;
        if (baseSet.contains(t)) return false;
        return added.add(t);
    }

    public void clear() {
        baseSet = Collections.emptySet();
        added.clear();
        removed.clear();
    }
    
    public boolean contains(Object t) {
        if (removed.contains(t)) return false;
        return baseSet.contains(t) || added.contains(t);
    }
    
    @SuppressWarnings("unchecked")
    public boolean remove(Object t) {
        assert invariantsSatisfied();
        if (added.remove(t)) return true;
        if (!baseSet.contains(t)) return false;
        return removed.add((T) t);
    }
    
    @SuppressWarnings("unchecked")
    public boolean retainAll(Collection coll) {
        if (coll == this) return false;
        if (coll instanceof DifferenceSet) {
            DifferenceSet other = (DifferenceSet) coll;
            if (other.baseSet == baseSet) {
                boolean changed = false;
                changed |= added.retainAll(other.added);
                changed |= removed.addAll(other.removed);
                assert invariantsSatisfied();
                return changed;
            }
        }
        if (coll.size() < size() / 2) {
            Set newSet = new HashSet(coll);
            newSet.retainAll(this);
            baseSet = Collections.emptySet();
            added = newSet;
            removed.clear();
            return true;
        }
        return super.retainAll(coll);
    }
    
    public int size() {
        return baseSet.size() + added.size() - removed.size();
    }
}
