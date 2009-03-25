// Copyright 2009 by Rob Shearer
package org.semanticweb.HermiT.util;

import java.io.PrintStream;

public class ConsoleMonitor implements TaskStatus {
    PrintStream stream;
    String name;
    long startTime = System.currentTimeMillis();
    long lastRefresh = 0;
    int numSteps = 0;
    int numDone = 0;
    
    public ConsoleMonitor(String name, PrintStream stream) {
        this.stream = stream;
        this.name = name;
        stream.print(name + "...");
    }
    
    public void setNumSteps(int total) {
        numSteps = total;
        itemsComplete(0, total);
    }
    
    public void step() {
        itemsComplete(numDone++, numSteps);
    }
    
    void itemsComplete(int numComplete, int numTotal) {
        if (System.currentTimeMillis() - lastRefresh < 200) return;
        lastRefresh = System.currentTimeMillis();
        int barWidth = 70 - name.length();
        for (int tot = numTotal; tot > 9; tot = tot / 10) barWidth -= 2;
        stream.print("\r" + name + ": [");
        int stepsComplete = (int) (numComplete / ((double) numTotal) * barWidth);
        for (int i = 0; i < stepsComplete; ++i) stream.print("*");
        for (int i = stepsComplete; i < barWidth; ++i) stream.print(" ");
        stream.print("] " + String.valueOf(numComplete) + "/" + String.valueOf(numTotal));
    }
    public void done() {
        lastRefresh = 0;
        if (numSteps > 0) itemsComplete(numSteps, numSteps);
        double taskTime = (System.currentTimeMillis() - startTime) / 1000.0;
        stream.println("");
        stream.println("Finished " + name +
            " (" + String.format("%.2g", taskTime) + " seconds)");
    }
    public TaskStatus subTask(String name) {
        if (numSteps > 0) step();
        stream.println("");
        return new ConsoleMonitor(name, stream);
    }
}
