// Copyright 2009 by Rob Shearer
package org.semanticweb.HermiT.util;

public interface TaskStatus {
    void setNumSteps(int total);
    void step();
    TaskStatus subTask(String name);
    void done();
}
