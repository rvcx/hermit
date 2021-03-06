// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT.tableau;

import java.io.Serializable;

/**
 * The actual implementation of the tuple tables used in the ExtensionTable 
 * class. 
 */
public final class TupleTable implements Serializable {
    private static final long serialVersionUID=-7712458276004062803L;

    private static final int PAGE_SIZE=512;   // Must be a power of two!

    private final int m_arity;
    private Page[] m_pages;
    private int m_numberOfPages;
    private int m_tupleCapacity;
    private int m_firstFreeTupleIndex;
    
    public TupleTable(int arity) {
        m_arity=arity;
        m_pages=new Page[10];
        m_numberOfPages=1;
        for (int i=0;i<m_numberOfPages;i++)
            m_pages[i]=new Page();
        m_tupleCapacity=m_numberOfPages*PAGE_SIZE;
        m_firstFreeTupleIndex=0;
    }
    public int sizeInMemory() {
        int size=m_pages.length*4;
        for (int i=m_pages.length-1;i>=0;--i)
            if (m_pages[i]!=null)
                size+=m_pages[i].sizeInMemory();
        return size;
    }
    public int getFirstFreeTupleIndex() {
        return m_firstFreeTupleIndex;
    }
    public int addTuple(Object[] tupleBuffer) {
        int newTupleIndex=m_firstFreeTupleIndex;
        if (newTupleIndex==m_tupleCapacity) {
            if (m_numberOfPages==m_pages.length) {
                Page[] newPages=new Page[m_numberOfPages*3/2];
                System.arraycopy(m_pages,0,newPages,0,m_numberOfPages);
                m_pages=newPages;
            }
            m_pages[m_numberOfPages++]=new Page();
            m_tupleCapacity+=PAGE_SIZE;
        }
        m_pages[newTupleIndex / PAGE_SIZE].storeTuple((newTupleIndex % PAGE_SIZE)*m_arity,tupleBuffer);
        m_firstFreeTupleIndex++;
        return newTupleIndex;
    }
    public boolean tupleEquals(Object[] tupleBuffer,int tupleIndex,int compareLength) {
        return m_pages[tupleIndex / PAGE_SIZE].tupleEquals(tupleBuffer,(tupleIndex % PAGE_SIZE)*m_arity,compareLength);
    }
    public void retrieveTuple(Object[] tupleBuffer,int tupleIndex) {
        m_pages[tupleIndex / PAGE_SIZE].retrieveTuple((tupleIndex % PAGE_SIZE)*m_arity,tupleBuffer);
    }
    public Object getTupleObject(int tupleIndex,int objectIndex) {
        assert objectIndex < m_arity;
        return m_pages[tupleIndex / PAGE_SIZE].m_objects[(tupleIndex % PAGE_SIZE)*m_arity+objectIndex];
    }
    public void setTupleObject(int tupleIndex,int objectIndex,Object object) {
        m_pages[tupleIndex / PAGE_SIZE].m_objects[(tupleIndex % PAGE_SIZE)*m_arity+objectIndex]=object;
    }
    public void truncate(int newFirstFreeTupleIndex) {
        m_firstFreeTupleIndex=newFirstFreeTupleIndex;
    }
    public void nullifyTuple(int tupleIndex) {
        m_pages[tupleIndex / PAGE_SIZE].nullifyTuple((tupleIndex % PAGE_SIZE)*m_arity);
    }
    public void clear() {
        m_firstFreeTupleIndex=0;
    }

    private final class Page implements Serializable {
        private static final long serialVersionUID=2239482172592108644L;

        public Object[] m_objects;
        
        public Page() {
            m_objects=new Object[m_arity*PAGE_SIZE];
        }
        public int sizeInMemory() {
            return m_objects.length*4;
        }
        public void storeTuple(int tupleStartIndex,Object[] tupleBuffer) {
            System.arraycopy(tupleBuffer,0,m_objects,tupleStartIndex,tupleBuffer.length);
        }
        public void retrieveTuple(int tupleStartIndex,Object[] tupleBuffer) {
            System.arraycopy(m_objects,tupleStartIndex,tupleBuffer,0,tupleBuffer.length);
        }
        public void nullifyTuple(int tupleStartIndex) {
            for (int index=0;index<m_arity;index++)
                m_objects[tupleStartIndex+index]=null;
        }
        public boolean tupleEquals(Object[] tupleBuffer,int tupleStartIndex,int compareLength) {
            int sourceIndex=compareLength-1;
            int targetIndex=tupleStartIndex+sourceIndex;
            while (sourceIndex>=0) {
                if (!tupleBuffer[sourceIndex].equals(m_objects[targetIndex]))
                    return false;
                sourceIndex--;
                targetIndex--;
            }
            return true;
        }
    }
}
