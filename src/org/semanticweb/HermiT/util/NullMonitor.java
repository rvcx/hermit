// Copyright 2009 by Rob Shearer
package org.semanticweb.HermiT.util;

public class NullMonitor implements TaskStatus {
    public void setNumSteps(int total) {}
    public void step() {}
    public TaskStatus subTask(String name) { return this; }
    public void done() {}
}
