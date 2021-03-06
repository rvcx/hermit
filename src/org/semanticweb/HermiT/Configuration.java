/**
 * 
 */
package org.semanticweb.HermiT;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.Serializable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.monitor.TableauMonitor;

public class Configuration implements Serializable,Cloneable {
    private static final long serialVersionUID=7741510316249774519L;

    public static enum TableauMonitorType {
        NONE,TIMING,TIMING_WITH_PAUSE,DEBUGGER_NO_HISTORY,DEBUGGER_HISTORY_ON
    }

    public static enum DirectBlockingType {
        SINGLE,PAIR_WISE,OPTIMAL
    }

    public static enum BlockingStrategyType {
        ANYWHERE,ANCESTOR
    }

    public static enum BlockingSignatureCacheType {
        CACHED,NOT_CACHED
    }

    public static enum ExistentialStrategyType {
        CREATION_ORDER,EL,INDIVIDUAL_REUSE
    }

    public Configuration.TableauMonitorType tableauMonitorType;
    public Configuration.DirectBlockingType directBlockingType;
    public Configuration.BlockingStrategyType blockingStrategyType;
    public Configuration.BlockingSignatureCacheType blockingSignatureCacheType;
    public Configuration.ExistentialStrategyType existentialStrategyType;
    public boolean checkClauses;
    public boolean prepareForExpressiveQueries;
    public boolean ignoreUnsupportedDatatypes;
    public TableauMonitor monitor;
    public HashMap<String,Object> parameters;

    public Configuration() {
        tableauMonitorType=Configuration.TableauMonitorType.NONE;
        directBlockingType=Configuration.DirectBlockingType.OPTIMAL;
        blockingStrategyType=Configuration.BlockingStrategyType.ANYWHERE;
        blockingSignatureCacheType=Configuration.BlockingSignatureCacheType.CACHED;
        existentialStrategyType=Configuration.ExistentialStrategyType.CREATION_ORDER;
        ignoreUnsupportedDatatypes=false;
        checkClauses=true;
        prepareForExpressiveQueries=false;
        monitor=null;
        parameters=new HashMap<String,Object>();
    }
    protected void setIndividualReuseStrategyReuseAlways(Set<? extends AtomicConcept> concepts) {
        parameters.put("IndividualReuseStrategy.reuseAlways",concepts);
    }
    public void loadIndividualReuseStrategyReuseAlways(File file) throws IOException {
        Set<AtomicConcept> concepts=loadConceptsFromFile(file);
        setIndividualReuseStrategyReuseAlways(concepts);
    }
    protected void setIndividualReuseStrategyReuseNever(Set<? extends AtomicConcept> concepts) {
        parameters.put("IndividualReuseStrategy.reuseNever",concepts);
    }
    public void loadIndividualReuseStrategyReuseNever(File file) throws IOException {
        Set<AtomicConcept> concepts=loadConceptsFromFile(file);
        setIndividualReuseStrategyReuseNever(concepts);
    }
    protected Set<AtomicConcept> loadConceptsFromFile(File file) throws IOException {
        Set<AtomicConcept> result=new HashSet<AtomicConcept>();
        BufferedReader reader=new BufferedReader(new FileReader(file));
        try {
            String line=reader.readLine();
            while (line!=null) {
                result.add(AtomicConcept.create(line));
                line=reader.readLine();
            }
            return result;
        }
        finally {
            reader.close();
        }
    }
    @SuppressWarnings("unchecked")
    public Configuration clone() {
        try {
            Configuration result=(Configuration)super.clone();
            result.parameters=(HashMap<String,Object>)parameters.clone();
            return result;
        }
        catch (CloneNotSupportedException cantHappen) {
            return null;
        }
    }
}