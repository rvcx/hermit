// Copyright 2009 by Rob Shearer
package org.semanticweb.HermiT;

import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;

import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLPredicate;
import org.semanticweb.HermiT.model.Variable;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicRole;

public class Rewriting {
    
    public static Set<DLClause> limitPredicateBranch(Set<DLClause> clauses,
                                                     int maxBranch,
                                                     Set<AtomicConcept> concepts,
                                                     Set<AtomicRole> objectRoles) {
        System.err.println(clauses.size() + " clauses before branch reduction");
        int branchNum = 0;
        
        Set<DLClause> out = new HashSet<DLClause>();
        Map<DLPredicate, Set<DLClause>> map
            = new HashMap<DLPredicate, Set<DLClause>>();
        for (DLClause c : clauses) {
            for (int i = 0; i < c.getBodyLength(); ++i) {
                DLPredicate pred = c.getBodyAtom(i).getDLPredicate();
                Set<DLClause> s = map.get(pred);
                if (s == null) {
                    s = new HashSet<DLClause>();
                    map.put(pred, s);
                }
                s.add(c);
            }
        }
        for (Map.Entry<DLPredicate, Set<DLClause>> e : map.entrySet()) {
            if (e.getValue().size() > maxBranch) {
                System.err.println(e.getKey().getArity() + "-pred "
                                    + e.getKey().toString() + " involved in "
                                    + String.valueOf(e.getValue().size())
                                    + " clauses.");
                DLPredicate pred = e.getKey();
                Variable xVar = Variable.create("X");
                Variable yVar = Variable.create("Y");
                int branchWidth
                    = (int) Math.sqrt((double) e.getValue().size());
                ArrayList<AtomicConcept> guards
                    = new ArrayList<AtomicConcept>();
                ArrayList<DLPredicate> triggers
                    = new ArrayList<DLPredicate>();
                for (int i = 0; i < branchWidth; ++i) {
                    guards.add(AtomicConcept.create
                        ("internal:branchGuard" + branchNum));
                    concepts.add(guards.get(i));
                    if (pred.getArity() == 1) {
                        triggers.add(AtomicConcept.create
                            ("internal:branchTrigger" + branchNum++));
                        concepts.add((AtomicConcept) triggers.get(i));
                        clauses.add(DLClause.create(
                            new Atom[] { Atom.create(triggers.get(i), xVar) },
                            new Atom[] { Atom.create(pred, xVar),
                                         Atom.create(guards.get(i), xVar) }));
                    } else {
                        assert pred.getArity() == 2;
                        triggers.add(AtomicRole.createAtomicRole
                            ("internal:branchTrigger" + branchNum++));
                        objectRoles.add((AtomicRole) triggers.get(i));
                        clauses.add(DLClause.create(
                            new Atom[] { Atom.create(triggers.get(i), xVar, yVar) },
                            new Atom[] { Atom.create(pred, xVar, yVar),
                                         Atom.create(guards.get(i), xVar) }));
                    }
                }
                
                int curBranch = 0;
                for (DLClause clause : e.getValue()) {
                    if (!clauses.contains(clause)) continue;
                    ++curBranch;
                    curBranch %= branchWidth;
                    List<Atom> body = new ArrayList<Atom>();
                    List<Atom> head = new ArrayList<Atom>();
                    List<Atom> trigAtoms = new ArrayList<Atom>();
                    for (int i = 0; i < clause.getBodyLength(); ++i) {
                        Atom atom = clause.getBodyAtom(i);
                        if (atom.getDLPredicate().equals(pred)) {
                            head.add(Atom.create(guards.get(curBranch),
                                                 atom.getArgument(0)));
                            if (pred.getArity() == 1) {
                                trigAtoms.add(
                                    Atom.create(triggers.get(curBranch),
                                                atom.getArgument(0)));
                            } else {
                                assert pred.getArity() == 2;
                                trigAtoms.add(
                                    Atom.create(triggers.get(curBranch),
                                                atom.getArgument(0),
                                                atom.getArgument(1)));
                            }
                        } else {
                            body.add(atom);
                        }
                    }
                    clauses.add(
                        DLClause.create(head.toArray(new Atom[0]),
                                        body.toArray(new Atom[0])));
                    
                    body.addAll(trigAtoms);
                    head.clear();
                    for (int i = 0; i < clause.getHeadLength(); ++i) {
                        head.add(clause.getHeadAtom(i));
                    }
                    clauses.add(
                        DLClause.create(head.toArray(new Atom[0]),
                                        body.toArray(new Atom[0])));
                    
                    clauses.remove(clause);
                }
            }
        }
        System.err.println(clauses.size() + " clauses after branch reduction");
        return clauses;

    }

}