// Copyright 2008 by Oxford University; see license.txt for details
package org.semanticweb.HermiT;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.Serializable;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.semanticweb.HermiT.blocking.AncestorBlocking;
import org.semanticweb.HermiT.blocking.AnywhereBlocking;
import org.semanticweb.HermiT.blocking.BlockingSignatureCache;
import org.semanticweb.HermiT.blocking.BlockingStrategy;
import org.semanticweb.HermiT.blocking.DirectBlockingChecker;
import org.semanticweb.HermiT.blocking.PairWiseDirectBlockingChecker;
import org.semanticweb.HermiT.blocking.SingleDirectBlockingChecker;
import org.semanticweb.HermiT.debugger.Debugger;
import org.semanticweb.HermiT.existentials.CreationOrderStrategy;
import org.semanticweb.HermiT.existentials.ExpansionStrategy;
import org.semanticweb.HermiT.existentials.IndividualReuseStrategy;
import org.semanticweb.HermiT.hierarchy.Classifier;
import org.semanticweb.HermiT.hierarchy.Hierarchy;
import org.semanticweb.HermiT.hierarchy.HierarchyPosition;
import org.semanticweb.HermiT.hierarchy.NaiveHierarchyPosition;
import org.semanticweb.HermiT.hierarchy.PositionTranslator;
import org.semanticweb.HermiT.hierarchy.TableauFunc;
import org.semanticweb.HermiT.hierarchy.TableauSubsumptionChecker;
import org.semanticweb.HermiT.hierarchy.TranslatedHierarchyPosition;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLOntology;
import org.semanticweb.HermiT.model.DescriptionGraph;
import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.HermiT.model.InverseRole;
import org.semanticweb.HermiT.model.Role;
import org.semanticweb.HermiT.monitor.TableauMonitor;
import org.semanticweb.HermiT.monitor.TableauMonitorFork;
import org.semanticweb.HermiT.monitor.Timer;
import org.semanticweb.HermiT.monitor.TimerWithPause;
import org.semanticweb.HermiT.owlapi.structural.BuiltInPropertyManager;
import org.semanticweb.HermiT.owlapi.structural.OWLAxioms;
import org.semanticweb.HermiT.owlapi.structural.OWLAxiomsExpressivity;
import org.semanticweb.HermiT.owlapi.structural.OWLClausification;
import org.semanticweb.HermiT.owlapi.structural.OWLHasKeyDummy;
import org.semanticweb.HermiT.owlapi.structural.OWLNormalization;
import org.semanticweb.HermiT.owlapi.structural.TransitivityManager;
import org.semanticweb.HermiT.tableau.Tableau;
import org.semanticweb.HermiT.util.GraphUtils;
import org.semanticweb.HermiT.util.TranslatedMap;
import org.semanticweb.HermiT.util.Translator;
import org.semanticweb.owl.apibinding.OWLManager;
import org.semanticweb.owl.model.OWLAxiom;
import org.semanticweb.owl.model.OWLClass;
import org.semanticweb.owl.model.OWLDataFactory;
import org.semanticweb.owl.model.OWLDataProperty;
import org.semanticweb.owl.model.OWLDescription;
import org.semanticweb.owl.model.OWLException;
import org.semanticweb.owl.model.OWLIndividual;
import org.semanticweb.owl.model.OWLObjectProperty;
import org.semanticweb.owl.model.OWLObjectPropertyExpression;
import org.semanticweb.owl.model.OWLOntology;
import org.semanticweb.owl.model.OWLOntologyManager;
import org.semanticweb.HermiT.hierarchy.Taxonomy;
import org.semanticweb.HermiT.hierarchy.TaxonomyHierarchy;

/**
 * Answers queries about the logical implications of a particular knowledge 
 * base. A Reasoner is associated with a single knowledge base, which is 
 * "loaded" when the reasoner is constructed. By default a full classification 
 * of all atomic terms in the knowledge base is also performed at this time 
 * (which can take quite a while for large or complex ontologies), but this 
 * behavior can be disabled as a part of the Reasoner configuration. Internal 
 * details of the loading and reasoning algorithms can be configured in the 
 * Reasoner constructor and do not change over the lifetime of the Reasoner 
 * object---internal data structures and caches are optimized for a particular 
 * configuration. By default, HermiT will use the set of options which provide 
 * optimal performance.

 */
public class Reasoner implements Serializable {
    private static final long serialVersionUID=-8277117863937974032L;

    // these four are never null:
    private final Configuration configuration;
    private final DLOntology dlOntology;
    private final Namespaces namespaces;
    private final Tableau tableau;
    
    // these three might be null, and are created on demand by `get...` methods:
    private Map<AtomicRole,HierarchyPosition<AtomicRole>> roleHierarchy;
    private Hierarchy<AtomicConcept> conceptHierarchy;
    private Map<AtomicConcept, Set<Individual>> realization;
    
    public Namespaces getNamespaces() {
        return namespaces;
    }

    @Deprecated
    public void seedSubsumptionCache() {
        cacheClassHierarchy();
    }
    
    public void cacheClassHierarchy() {
        getConceptHierarchy();
    }
    
    @Deprecated
    public boolean isSubsumptionCacheSeeded() {
        return isClassHierarchyCached();
    }
    
    public boolean isClassHierarchyCached() {
        return conceptHierarchy != null;
    }
    
    public void cacheRealization() {
        getRealization();
    }
    
    public boolean isRealizationCached() {
        return realization != null;
    }
    
    private Hierarchy<AtomicConcept> getConceptHierarchy() {
        if (conceptHierarchy == null) {
            Set<AtomicConcept> allConcepts = new HashSet<AtomicConcept>();
            for (AtomicConcept c : dlOntology.getAllAtomicConcepts()) {
                if (!Namespaces.isInternalURI(c.getURI())) {
                    allConcepts.add(c);
                }
            }
            Map<AtomicConcept, Set<AtomicConcept>> known
                = new HashMap<AtomicConcept, Set<AtomicConcept>>();
            for (AtomicConcept c : allConcepts) {
                Set<AtomicConcept> s = new HashSet<AtomicConcept>();
                s.add(c);
                known.put(c, s);
            }
            Taxonomy<AtomicConcept> tax = new Taxonomy<AtomicConcept>(
                new Taxonomy.Ordering<AtomicConcept>() {
                    public boolean doesPrecede(AtomicConcept child,
                                               AtomicConcept parent) {
                        return tableau.isSubsumedBy(child, parent);
                    }
                },
                known, null // TODO: set these!
            );
            conceptHierarchy = new TaxonomyHierarchy<AtomicConcept>(tax);
        }
        return conceptHierarchy;
    }
    
    void outputClauses(java.io.PrintWriter output, Namespaces namespaces) {
        output.println(dlOntology.toString(namespaces));
    }
    
    public Reasoner(String ontologyURI)
        throws IllegalArgumentException, OWLException {
        this(new Configuration(),URI.create(ontologyURI));
    }

    public Reasoner(java.net.URI ontologyURI)
        throws IllegalArgumentException,OWLException {
        this(new Configuration(),ontologyURI);
    }

    public Reasoner(Configuration configuration, java.net.URI ontologyURI)
        throws IllegalArgumentException,OWLException {
        this(configuration,ontologyURI, (Set<DescriptionGraph>) null,
             (Set<OWLHasKeyDummy>) null);
    }

    public Reasoner(Configuration configuration,
                    OWLOntologyManager ontologyManger,
                    OWLOntology ontology) {
        this(configuration, ontologyManger, ontology,
             (Set<DescriptionGraph>) null, (Set<OWLHasKeyDummy>) null);
    }

    public Reasoner(Configuration configuration, java.net.URI ontologyURI,
                    Set<DescriptionGraph> descriptionGraphs,
                    Set<OWLHasKeyDummy> keys)
        throws IllegalArgumentException,OWLException {
        if (descriptionGraphs == null) {
            descriptionGraphs = Collections.emptySet();
        }
        if (keys == null) {
            keys = Collections.emptySet();
        }
        OWLOntologyManager ontologyManager
            = OWLManager.createOWLOntologyManager();
        OWLOntology ontology
            = ontologyManager.loadOntologyFromPhysicalURI(ontologyURI);
        OWLClausification clausifier
            = new OWLClausification(configuration);
        dlOntology = clausifier.clausifyWithKeys(ontologyManager, ontology,
                                                 descriptionGraphs, keys);
        this.configuration = configuration;
        this.namespaces = new Namespaces(dlOntology);
        this.tableau = createTableau(configuration, dlOntology, namespaces);
    }

    public Reasoner(Configuration configuration,
                    OWLOntologyManager ontologyManager,
                    OWLOntology ontology,
                    Set<DescriptionGraph> descriptionGraphs,
                    Set<OWLHasKeyDummy> keys) {
        OWLClausification clausifier = new OWLClausification(configuration);
        if (descriptionGraphs == null) {
            descriptionGraphs = Collections.emptySet();
        }
        if (keys == null) {
            keys = Collections.emptySet();
        }
        this.configuration = configuration;
        dlOntology = clausifier.clausifyWithKeys(ontologyManager, ontology,
                                                 descriptionGraphs, keys);
        namespaces = new Namespaces(dlOntology);
        tableau = createTableau(configuration, dlOntology, namespaces);
    }
    
    /**
     * Creates a reasoner that contains all axioms from the ontologies in the 
     * 'ontologies'' parameter. If any ontology in this collection contains 
     * imports, these are *NOT* traversed -- that is, the resulting ontology 
     * contains *EXACTLY* the axioms explciitly present in the supplied 
     * ontologies. The resulting DL ontology has the URI ontologyURI.
     */
    public Reasoner(Configuration configuration,
                    OWLOntologyManager ontologyManger,
                    Collection<OWLOntology> importClosure,
                    String ontologyURI) {
        OWLClausification clausifier = new OWLClausification(configuration);
        Set<OWLHasKeyDummy> keys = Collections.emptySet();
        Set<DescriptionGraph> dgs = Collections.emptySet();
        this.configuration = configuration;
        dlOntology = clausifier.clausifyImportClosure
            (ontologyManger.getOWLDataFactory(), ontologyURI,
             importClosure, dgs, keys);
        namespaces = new Namespaces(dlOntology);
        tableau = createTableau(configuration, dlOntology, namespaces);
    }

    public Reasoner(Configuration configuration, DLOntology dlOntology) {
        this.configuration = configuration;
        this.dlOntology = dlOntology;
        namespaces = new Namespaces(dlOntology);
        tableau = createTableau(configuration, dlOntology, namespaces);
    }

    /**
     * Return `true` iff `classUri` occurred in the loaded knowledge base.
     */
    public boolean isClassNameDefined(String classUri) {
        return dlOntology.getAllAtomicConcepts().contains
                    (AtomicConcept.create(classUri))
            || classUri.equals(AtomicConcept.THING.getURI())
            || classUri.equals(AtomicConcept.NOTHING.getURI());
    }
    
    public Set<String> getDefinedClassNames() {
        Set<String> out = new HashSet<String>();
        out.add(AtomicConcept.THING.getURI());
        out.add(AtomicConcept.NOTHING.getURI());
        for (AtomicConcept c : dlOntology.getAllAtomicConcepts()) {
            if (!Namespaces.isInternalURI(c.getURI())) {
                out.add(c.getURI());
            }
        }
        return out;
    }

    // General inferences
    
    public boolean isConsistent() {
        return tableau.isABoxSatisfiable();
    }

    // Concept inferences
    
    public boolean isClassSatisfiable(String classURI) {
        return tableau.isSatisfiable(AtomicConcept.create(classURI));
    }

    public boolean isSatisfiable(OWLDescription description) {
        if (description instanceof OWLClass) {
            return isClassSatisfiable(((OWLClass) description).getURI().toString());
        } else {
            OWLOntologyManager ontologyManager = OWLManager.createOWLOntologyManager();
            OWLDataFactory factory = ontologyManager.getOWLDataFactory();
            OWLClass newClass = factory.getOWLClass(URI.create("internal:query-concept"));
            OWLAxiom classDefinitionAxiom = factory.getOWLSubClassAxiom(newClass,description);
            DLOntology newDLOntology = extendDLOntology(configuration,
                                                        namespaces,
                                                        "uri:urn:internal-kb",
                                                        dlOntology,
                                                        ontologyManager,
                                                        classDefinitionAxiom);
            Tableau tempTableau
                = createTableau(configuration, newDLOntology, namespaces);
            return tempTableau.isSatisfiable
                    (AtomicConcept.create("internal:query-concept"));
        }
    }

    public boolean isClassSubsumedBy(String childName,String parentName) {
        return tableau.isSubsumedBy(AtomicConcept.create(childName),
                                    AtomicConcept.create(parentName));
    }

    public boolean isSubsumedBy(OWLDescription subDescription,
                                OWLDescription superDescription) {
        if (   subDescription instanceof OWLClass
            && superDescription instanceof OWLClass) {
            return isClassSubsumedBy(
                        ((OWLClass) subDescription).getURI().toString(),
                        ((OWLClass) superDescription).getURI().toString()
                    );
        } else {
            OWLOntologyManager ontologyManager
                = OWLManager.createOWLOntologyManager();
            OWLDataFactory factory = ontologyManager.getOWLDataFactory();
            OWLClass newSubConcept
                = factory.getOWLClass(URI.create("internal:query-subconcept"));
            OWLAxiom subClassDefinitionAxiom
                = factory.getOWLSubClassAxiom(newSubConcept,subDescription);
            OWLClass newSuperConcept
                = factory.getOWLClass(URI.create("internal:query-superconcept"));
            OWLAxiom superClassDefinitionAxiom
                = factory.getOWLSubClassAxiom(superDescription,newSuperConcept);
            DLOntology newDLOntology = extendDLOntology(configuration,
                                                        namespaces,
                                                        "uri:urn:internal-kb",
                                                        dlOntology,
                                                        ontologyManager,
                                                        subClassDefinitionAxiom,
                                                        superClassDefinitionAxiom);
            Tableau tempTableau
                = createTableau(configuration, newDLOntology, namespaces);
            return tempTableau.isSubsumedBy(
                    AtomicConcept.create("internal:query-subconcept"),
                    AtomicConcept.create("internal:query-superconcept")
            );
        }
    }

    // Concept hierarchy

    @Deprecated
    public HierarchyPosition<String> getClassHierarchyPosition(String className) {
        return getHierarchyPositionForClass(className);
    }
    
    public HierarchyPosition<String> getHierarchyPositionForClass(String className)
        throws IllegalArgumentException {
        if (!isClassNameDefined(className)) {
            throw new IllegalArgumentException(
                "Class '" + className + "' does not occur in the loaded ontology."
            );
        }
        return new TranslatedHierarchyPosition<AtomicConcept, String>
            (getHierarchyPosition(AtomicConcept.create(className)),
             new ConceptToString());
    }

    public HierarchyPosition<OWLClass> getHierarchyPosition(OWLDescription description) {
        OWLOntologyManager ontologyManager
            = OWLManager.createOWLOntologyManager();
        OWLDataFactory factory = ontologyManager.getOWLDataFactory();
        HierarchyPosition<AtomicConcept> hierarchyPosition;
        if (description instanceof OWLClass) {
            AtomicConcept atomicConcept
                = AtomicConcept.create(
                        ((OWLClass) description).getURI().toString());
            hierarchyPosition = getHierarchyPosition(atomicConcept);
        } else {
            OWLClass newClass
                = factory.getOWLClass(URI.create("internal:query-concept"));
            OWLAxiom classDefinitionAxiom
                = factory.getOWLEquivalentClassesAxiom(newClass,description);
            DLOntology newDLOntology
                = extendDLOntology(configuration,
                                   namespaces,
                                   "uri:urn:internal-kb",
                                   dlOntology,
                                   ontologyManager,
                                   classDefinitionAxiom);
            Tableau tempTableau
                = createTableau(configuration, newDLOntology, namespaces);
            hierarchyPosition = getHierarchyPosition(
                AtomicConcept.create("internal:query-concept"), tempTableau);
        }
        return new TranslatedHierarchyPosition<AtomicConcept,OWLClass>
            (hierarchyPosition, new ConceptToOWLClass(factory));
    }

    private HierarchyPosition<AtomicConcept>
        getHierarchyPosition(AtomicConcept atomicConcept) {
        return getHierarchyPosition(atomicConcept, tableau);
    }
    
    private HierarchyPosition<AtomicConcept>
        getHierarchyPosition(final AtomicConcept concept,
                             final Tableau tableau) {
        return getConceptHierarchy().getPosition(
            new Hierarchy.Element<AtomicConcept>() {
                public boolean doesPrecede(AtomicConcept other) {
                    return tableau.isSubsumedBy(concept, other);
                }
                public boolean doesSucceed(AtomicConcept other) {
                    return tableau.isSubsumedBy(other, concept);
                }
                public AtomicConcept getEquivalent() {
                    return concept;
                }
            });
    }
    
    // Object property inferences
    
    public boolean isAsymmetric(OWLObjectProperty p) {
        return tableau.isAsymmetric(
            AtomicRole.createAtomicRole(p.getURI().toString()));
    }

    // Property hierarchy
    
    @Deprecated
    public HierarchyPosition<String> getPropertyHierarchyPosition(String propertyURI) {
        return getHierarchyPositionForProperty(propertyURI);
    }
    
    public HierarchyPosition<String> getHierarchyPositionForProperty(String propertyURI) {
        AtomicRole atomicRole=AtomicRole.createAtomicRole(propertyURI);
        if (dlOntology.getAllAtomicDataRoles().contains(atomicRole))
            return new TranslatedHierarchyPosition<AtomicRole,String>(getHierarchyPosition(AtomicRole.createAtomicRole(propertyURI),AtomicRole.TOP_DATA_ROLE,AtomicRole.BOTTOM_DATA_ROLE),new RoleToString());
        else
            return new TranslatedHierarchyPosition<AtomicRole,String>(getHierarchyPosition(AtomicRole.createAtomicRole(propertyURI),AtomicRole.TOP_OBJECT_ROLE,AtomicRole.BOTTOM_OBJECT_ROLE),new RoleToString());
    }
    
    public HierarchyPosition<OWLObjectProperty> getHierarchyPosition(OWLObjectProperty p) {
        OWLDataFactory factory=OWLManager.createOWLOntologyManager().getOWLDataFactory();
        return new TranslatedHierarchyPosition<AtomicRole,OWLObjectProperty>(getHierarchyPosition(AtomicRole.createAtomicRole(p.getURI().toString()),AtomicRole.TOP_OBJECT_ROLE,AtomicRole.BOTTOM_OBJECT_ROLE),new RoleToOWLObjectProperty(factory));
    }

    public HierarchyPosition<OWLDataProperty> getHierarchyPosition(OWLDataProperty p) {
        OWLDataFactory factory=OWLManager.createOWLOntologyManager().getOWLDataFactory();
        return new TranslatedHierarchyPosition<AtomicRole,OWLDataProperty>(getHierarchyPosition(AtomicRole.createAtomicRole(p.getURI().toString()),AtomicRole.TOP_DATA_ROLE,AtomicRole.BOTTOM_DATA_ROLE),new RoleToOWLDataProperty(factory));
    }

    private Map<AtomicRole,HierarchyPosition<AtomicRole>> getRoleHierarchy() {
        if (roleHierarchy==null) {
            final Map<Role,Set<Role>> subRoles=new HashMap<Role,Set<Role>>();
            for (DLClause dlClause : dlOntology.getDLClauses()) {
                if (dlClause.isRoleInclusion()) {
                    Role sub=(Role)dlClause.getBodyAtom(0).getDLPredicate();
                    Role sup=(Role)dlClause.getHeadAtom(0).getDLPredicate();
                    addInclusion(subRoles,sub,sup);
                    addInclusion(subRoles,sub.getInverse(),sup.getInverse());
                }
                else if (dlClause.isRoleInverseInclusion()) {
                    Role sub=(Role)dlClause.getBodyAtom(0).getDLPredicate();
                    Role sup=((Role)dlClause.getHeadAtom(0).getDLPredicate()).getInverse();
                    addInclusion(subRoles,sub,sup);
                    addInclusion(subRoles,sub.getInverse(),sup.getInverse());
                }
            }
            GraphUtils.transitivelyClose(subRoles);
            NaiveHierarchyPosition.Ordering<AtomicRole> ordering=new NaiveHierarchyPosition.Ordering<AtomicRole>() {
                public boolean less(AtomicRole sub,AtomicRole sup) {
                    if (AtomicRole.TOP_DATA_ROLE.equals(sup) || AtomicRole.TOP_OBJECT_ROLE.equals(sup) || AtomicRole.BOTTOM_DATA_ROLE.equals(sub) || AtomicRole.BOTTOM_OBJECT_ROLE.equals(sub))
                        return true;
                    Set<Role> subs=subRoles.get(sup);
                    if (subs==null)
                        return false;
                    return subs.contains(sub);
                }
            };
            roleHierarchy=NaiveHierarchyPosition.buildHierarchy(AtomicRole.TOP_OBJECT_ROLE,AtomicRole.BOTTOM_OBJECT_ROLE,dlOntology.getAllAtomicObjectRoles(),ordering);
            roleHierarchy.putAll(NaiveHierarchyPosition.buildHierarchy(AtomicRole.TOP_DATA_ROLE,AtomicRole.BOTTOM_DATA_ROLE,dlOntology.getAllAtomicDataRoles(),ordering));
        }
        return roleHierarchy;
    }

    private static void addInclusion(Map<Role,Set<Role>> subRoles,Role sub,Role sup) {
        Set<Role> subs=subRoles.get(sup);
        if (subs==null) {
            subs=new HashSet<Role>();
            subRoles.put(sup,subs);
        }
        subs.add(sub);
    }

    private HierarchyPosition<AtomicRole> getHierarchyPosition(AtomicRole r,AtomicRole topRole,AtomicRole bottomRole) {
        HierarchyPosition<AtomicRole> out=getRoleHierarchy().get(r);
        if (out==null) {
            NaiveHierarchyPosition<AtomicRole> newPos=new NaiveHierarchyPosition<AtomicRole>(r);
            newPos.parents.add(getRoleHierarchy().get(topRole));
            newPos.children.add(getRoleHierarchy().get(bottomRole));
            out=newPos;
        }
        return out;
    }

    // Individual inferences
    
    public boolean isIndividualInstanceOfClass(String individualURI,
                                             String classURI) {
        return tableau.isInstanceOf(Individual.create(individualURI),
                                    AtomicConcept.create(classURI));
    }
    
    public boolean isInstanceOf(OWLIndividual individual,
                                OWLDescription description) {
        if (description instanceof OWLClass)
            return isIndividualInstanceOfClass(individual.getURI().toString(), ((OWLClass)description).getURI().toString());
        else {
            OWLOntologyManager ontologyManager=OWLManager.createOWLOntologyManager();
            OWLDataFactory factory=ontologyManager.getOWLDataFactory();
            OWLClass newClass=factory.getOWLClass(URI.create("internal:query-concept"));
            OWLAxiom classDefinitionAxiom=factory.getOWLSubClassAxiom(description,newClass);
            DLOntology newDLOntology=extendDLOntology(configuration,namespaces,"uri:urn:internal-kb",dlOntology,ontologyManager,classDefinitionAxiom);
            Tableau tableau=createTableau(configuration,newDLOntology,namespaces);
            return tableau.isInstanceOf(
                Individual.create(individual.getURI().toString()),
                AtomicConcept.create("internal:query-concept"));
        }
    }
    
    public HierarchyPosition<String> getHierarchyPositionOfIndividual(String individual) {
        return new TranslatedHierarchyPosition<AtomicConcept, String>
            (getHierarchyPosition(Individual.create(individual)),
             new ConceptToString());
    }

    public HierarchyPosition<OWLClass> getHierarchyPosition(OWLIndividual individual) {
        OWLDataFactory factory=OWLManager.createOWLOntologyManager().getOWLDataFactory();
        return new TranslatedHierarchyPosition<AtomicConcept,OWLClass>
            (getHierarchyPosition(Individual.create(individual.getURI().toString())),
             new ConceptToOWLClass(factory));
    }

    public Set<String> getMembersOfClass(String className) {
        Set<String> result=new HashSet<String>();
        for (AtomicConcept atomicConcept :
                getHierarchyPosition(AtomicConcept.create(className)).getDescendants()) {
            Set<Individual> realizationForConcept
                = getRealization().get(atomicConcept);
            // realizationForConcept could be null because of the way
            // realization is constructed; for example, concepts that don't
            // have direct instances are not entered into the realization at all.
            if (realizationForConcept != null) {
                for (Individual individual : realizationForConcept) {
                    result.add(individual.getURI());
                }
            }
        }
        return result;
    }

    public Set<OWLIndividual> getMembers(OWLDescription description) {
        HierarchyPosition<OWLClass> hierarchyPosition = getHierarchyPosition(description);
        OWLDataFactory factory=OWLManager.createOWLOntologyManager().getOWLDataFactory();
        Set<OWLIndividual> result=new HashSet<OWLIndividual>();
        loadIndividualsOfPosition(hierarchyPosition,result,factory);
        for (HierarchyPosition<OWLClass> descendantHierarchyPosition : hierarchyPosition.getDescendantPositions())
            loadIndividualsOfPosition(descendantHierarchyPosition,result,factory);
        return result;
    }
    
    private void loadIndividualsOfPosition(HierarchyPosition<OWLClass> position,Set<OWLIndividual> result,OWLDataFactory factory) {
        AtomicConcept atomicConcept=AtomicConcept.create(position.getEquivalents().iterator().next().getURI().toString());
        Set<Individual> realizationForConcept=getRealization().get(atomicConcept);
        // realizationForConcept could be null because of the way realization is constructed;
        // for example, concepts that don't have direct instances are not entered into the realization at all.
        if (realizationForConcept!=null)
            for (Individual individual : realizationForConcept)
                result.add(factory.getOWLIndividual(URI.create(individual.getURI())));
    }
    
    public Set<String> getDirectMembersOfClass(String className) {
        Set<String> result=new HashSet<String>();
        Set<Individual> realizationForConcept=getRealization().get(AtomicConcept.create(className));
        // realizationForConcept could be null because of the way realization is constructed;
        // for example, concepts that don't have direct instances are not entered into the realization at all.
        if (realizationForConcept!=null)
            for (Individual individual : realizationForConcept)
                result.add(individual.getURI());
        return result;
    }

    public Set<OWLIndividual> getDirectMembers(OWLDescription description) {
        HierarchyPosition<OWLClass> hierarchyPosition=getHierarchyPosition(description);
        OWLDataFactory factory=OWLManager.createOWLOntologyManager().getOWLDataFactory();
        Set<OWLIndividual> result=new HashSet<OWLIndividual>();
        Map<AtomicConcept,Set<Individual>> realization=getRealization();
        Set<OWLClass> children=hierarchyPosition.getEquivalents();
        if (children.isEmpty())
            for (HierarchyPosition<OWLClass> childPosition : hierarchyPosition.getChildPositions())
                children.addAll(childPosition.getEquivalents());
        for (OWLClass child : children) {
            Set<Individual> realizationForConcept=realization.get(AtomicConcept.create(child.getURI().toString()));
            // realizationForConcept could be null because of the way realization is constructed;
            // for example, concepts that don't have direct instances are not entered into the realization at all.
            if (realizationForConcept!=null)
                for (Individual individual : realizationForConcept)
                    result.add(factory.getOWLIndividual(URI.create(individual.getURI())));
        }
        return result;
    }

    private Map<AtomicConcept, Set<Individual>> getRealization() {
        if (realization == null) {
            realization = new HashMap<AtomicConcept,Set<Individual>>();
            for (Individual individual : dlOntology.getAllIndividuals()) {
                Set<AtomicConcept> mostSpecific = new HashSet<AtomicConcept>();
                HierarchyPosition<AtomicConcept> pos = getHierarchyPosition(individual);
                mostSpecific.addAll(pos.getEquivalents());
                if (mostSpecific.isEmpty()) {
                    for (HierarchyPosition<AtomicConcept> parent
                            : pos.getParentPositions()) {
                        mostSpecific.addAll(parent.getEquivalents());
                    }
                }
                for (AtomicConcept parent : mostSpecific) {
                    Set<Individual> set = realization.get(parent);
                    if (set == null) {
                        set = new HashSet<Individual>();
                        realization.put(parent, set);
                    }
                    set.add(individual);
                }
            }
        }
        return realization;
    }
    
    private HierarchyPosition<AtomicConcept>
        getHierarchyPosition(Individual individual) {
        // TODO: implement!
        // return conceptHierarchy.getPosition(
        return null;
    }

    private boolean isInstanceOf(Individual i,
                                   AtomicConcept c) {
        if (AtomicConcept.THING.equals(c)) {
            return true;
        } else {
            return tableau.isInstanceOf(i, c);
        }
    }
    
    
    // Various creation methods
    
    protected static Tableau createTableau(Configuration config,DLOntology dlOntology,Namespaces namespaces) throws IllegalArgumentException {
        if (!dlOntology.canUseNIRule() && dlOntology.hasAtMostRestrictions() && dlOntology.hasInverseRoles() && config.existentialStrategyType==Configuration.ExistentialStrategyType.INDIVIDUAL_REUSE)
            throw new IllegalArgumentException("The supplied DL-ontology is not compatible with the individual reuse strategy.");

        if (config.checkClauses) {
            Collection<DLClause> nonAdmissibleDLClauses=dlOntology.getNonadmissibleDLClauses();
            if (!nonAdmissibleDLClauses.isEmpty()) {
                String CRLF=System.getProperty("line.separator");
                StringBuffer buffer=new StringBuffer();
                buffer.append("The following DL-clauses in the DL-ontology"+" are not admissible:");
                buffer.append(CRLF);
                for (DLClause dlClause : nonAdmissibleDLClauses) {
                    buffer.append(dlClause.toString(namespaces));
                    buffer.append(CRLF);
                }
                throw new IllegalArgumentException(buffer.toString());
            }
        }

        TableauMonitor wellKnownTableauMonitor=null;
        switch (config.tableauMonitorType) {
        case NONE:
            wellKnownTableauMonitor=null;
            break;
        case TIMING:
            wellKnownTableauMonitor=new Timer();
            break;
        case TIMING_WITH_PAUSE:
            wellKnownTableauMonitor=new TimerWithPause();
            break;
        case DEBUGGER_HISTORY_ON:
            wellKnownTableauMonitor=new Debugger(namespaces,true);
            break;
        case DEBUGGER_NO_HISTORY:
            wellKnownTableauMonitor=new Debugger(namespaces,false);
            break;
        default:
            throw new IllegalArgumentException("Unknown monitor type");
        }

        TableauMonitor tableauMonitor=null;
        if (config.monitor==null)
            tableauMonitor=wellKnownTableauMonitor;
        else if (wellKnownTableauMonitor==null)
            tableauMonitor=config.monitor;
        else
            tableauMonitor=new TableauMonitorFork(wellKnownTableauMonitor,config.monitor);

        DirectBlockingChecker directBlockingChecker=null;
        switch (config.directBlockingType) {
        case OPTIMAL:
            if (dlOntology.hasAtMostRestrictions() && dlOntology.hasInverseRoles())
                directBlockingChecker=new PairWiseDirectBlockingChecker();
            else
                directBlockingChecker=new SingleDirectBlockingChecker();
            break;
        case SINGLE:
            directBlockingChecker=new SingleDirectBlockingChecker();
            break;
        case PAIR_WISE:
            directBlockingChecker=new PairWiseDirectBlockingChecker();
            break;
        default:
            throw new IllegalArgumentException("Unknown direct blocking type.");
        }

        BlockingSignatureCache blockingSignatureCache=null;
        if (!dlOntology.hasNominals()) {
            switch (config.blockingSignatureCacheType) {
            case CACHED:
                blockingSignatureCache=new BlockingSignatureCache(directBlockingChecker);
                break;
            case NOT_CACHED:
                blockingSignatureCache=null;
                break;
            default:
                throw new IllegalArgumentException("Unknown blocking cache type.");
            }
        }

        BlockingStrategy blockingStrategy=null;
        switch (config.blockingStrategyType) {
        case ANCESTOR:
            blockingStrategy=new AncestorBlocking(directBlockingChecker,blockingSignatureCache);
            break;
        case ANYWHERE:
            blockingStrategy=new AnywhereBlocking(directBlockingChecker,blockingSignatureCache);
            break;
        default:
            throw new IllegalArgumentException("Unknown blocking strategy type.");
        }

        ExpansionStrategy existentialsExpansionStrategy=null;
        switch (config.existentialStrategyType) {
        case CREATION_ORDER:
            existentialsExpansionStrategy=new CreationOrderStrategy(blockingStrategy);
            break;
        case EL:
            existentialsExpansionStrategy=new IndividualReuseStrategy(blockingStrategy,true);
            break;
        case INDIVIDUAL_REUSE:
            existentialsExpansionStrategy=new IndividualReuseStrategy(blockingStrategy,false);
            break;
        default:
            throw new IllegalArgumentException("Unknown expansion strategy type.");
        }

        return new Tableau(tableauMonitor,existentialsExpansionStrategy,dlOntology,config.parameters);
    }

    private static DLOntology extendDLOntology(Configuration config,
                                                 Namespaces namespaces,
                                                 String resultingOntologyURI,
                                                 DLOntology originalDLOntology,
                                                 OWLOntologyManager ontologyManager,
                                                 OWLAxiom... additionalAxioms)
        throws IllegalArgumentException {
        try {
            Set<DescriptionGraph> descriptionGraphs=Collections.emptySet();
            OWLDataFactory factory=ontologyManager.getOWLDataFactory();
            OWLOntology newOntology=ontologyManager.createOntology(URI.create("uri:urn:internal-kb"));
            for (OWLAxiom axiom : additionalAxioms)
                ontologyManager.addAxiom(newOntology,axiom);
            OWLAxioms axioms=new OWLAxioms();
            OWLNormalization normalization=new OWLNormalization(factory,axioms);
            normalization.processOntology(config,newOntology);
            if (!originalDLOntology.getAllAtomicObjectRoles().contains(AtomicRole.TOP_OBJECT_ROLE)) {
                BuiltInPropertyManager builtInPropertyManager=new BuiltInPropertyManager(factory);   
                builtInPropertyManager.axiomatizeTopObjectPropertyIfNeeded(axioms);
            }
            if (!originalDLOntology.getAllTransitiveObjectRoles().isEmpty() || !axioms.m_transitiveObjectProperties.isEmpty()) {
                TransitivityManager transitivityManager=new TransitivityManager(factory);
                transitivityManager.prepareTransformation(axioms);
                for (Role transitiveRole : originalDLOntology.getAllTransitiveObjectRoles()) {
                    OWLObjectPropertyExpression objectPropertyExpression=getObjectPropertyExpression(factory,transitiveRole);
                    transitivityManager.makeTransitive(objectPropertyExpression);
                }
                for (DLClause dlClause : originalDLOntology.getDLClauses()) {
                    if (dlClause.isRoleInclusion()) {
                        AtomicRole subAtomicRole=(AtomicRole)dlClause.getBodyAtom(0).getDLPredicate();
                        AtomicRole superAtomicRole=(AtomicRole)dlClause.getHeadAtom(0).getDLPredicate();
                        if (originalDLOntology.getAllAtomicObjectRoles().contains(subAtomicRole) && originalDLOntology.getAllAtomicObjectRoles().contains(superAtomicRole)) {
                            OWLObjectProperty subObjectProperty=getObjectProperty(factory,subAtomicRole);
                            OWLObjectProperty superObjectProperty=getObjectProperty(factory,superAtomicRole);
                            transitivityManager.addInclusion(subObjectProperty,superObjectProperty);
                        }
                    }
                    else if (dlClause.isRoleInverseInclusion()) {
                        AtomicRole subAtomicRole=(AtomicRole)dlClause.getBodyAtom(0).getDLPredicate();
                        AtomicRole superAtomicRole=(AtomicRole)dlClause.getHeadAtom(0).getDLPredicate();
                        if (originalDLOntology.getAllAtomicObjectRoles().contains(subAtomicRole) && originalDLOntology.getAllAtomicObjectRoles().contains(superAtomicRole)) {
                            OWLObjectProperty subObjectProperty=getObjectProperty(factory,subAtomicRole);
                            OWLObjectPropertyExpression superObjectPropertyExpression=getObjectProperty(factory,superAtomicRole).getInverseProperty();
                            transitivityManager.addInclusion(subObjectProperty,superObjectPropertyExpression);
                        }
                    }
                }
                transitivityManager.rewriteConceptInclusions(axioms);
            }
            OWLAxiomsExpressivity axiomsExpressivity=new OWLAxiomsExpressivity(axioms);
            axiomsExpressivity.m_hasAtMostRestrictions|=originalDLOntology.hasAtMostRestrictions();
            axiomsExpressivity.m_hasInverseRoles|=originalDLOntology.hasInverseRoles();
            axiomsExpressivity.m_hasNominals|=originalDLOntology.hasNominals();
            axiomsExpressivity.m_hasDatatypes|=originalDLOntology.hasDatatypes();
            OWLClausification clausifier=new OWLClausification(config);
            DLOntology newDLOntology=clausifier.clausify(ontologyManager.getOWLDataFactory(),"uri:urn:internal-kb",axioms,axiomsExpressivity,descriptionGraphs);
            
            Set<DLClause> dlClauses=createUnion(originalDLOntology.getDLClauses(),newDLOntology.getDLClauses());
            Set<Atom> positiveFacts=createUnion(originalDLOntology.getPositiveFacts(),newDLOntology.getPositiveFacts());
            Set<Atom> negativeFacts=createUnion(originalDLOntology.getNegativeFacts(),newDLOntology.getNegativeFacts());
            Set<AtomicConcept> atomicConcepts=createUnion(originalDLOntology.getAllAtomicConcepts(),newDLOntology.getAllAtomicConcepts());
            Set<Role> transitiveObjectRoles=createUnion(originalDLOntology.getAllTransitiveObjectRoles(),newDLOntology.getAllTransitiveObjectRoles());
            Set<AtomicRole> atomicObjectRoles=createUnion(originalDLOntology.getAllAtomicObjectRoles(),newDLOntology.getAllAtomicObjectRoles());
            Set<AtomicRole> atomicDataRoles=createUnion(originalDLOntology.getAllAtomicDataRoles(),newDLOntology.getAllAtomicDataRoles());
            Set<Individual> individuals=createUnion(originalDLOntology.getAllIndividuals(),newDLOntology.getAllIndividuals());
            boolean hasInverseRoles=originalDLOntology.hasInverseRoles() || newDLOntology.hasInverseRoles();
            boolean hasAtMostRestrictions=originalDLOntology.hasAtMostRestrictions() || newDLOntology.hasAtMostRestrictions();
            boolean hasNominals=originalDLOntology.hasNominals() || newDLOntology.hasNominals();
            boolean canUseNIRule=originalDLOntology.canUseNIRule() || newDLOntology.canUseNIRule();
            boolean hasDatatypes=originalDLOntology.hasDatatypes() || newDLOntology.hasDatatypes();
            return new DLOntology(resultingOntologyURI,dlClauses,positiveFacts,negativeFacts,atomicConcepts,transitiveObjectRoles,atomicObjectRoles,atomicDataRoles,individuals,hasInverseRoles,hasAtMostRestrictions,hasNominals,canUseNIRule,hasDatatypes);
        }
        catch (OWLException shouldntHappen) {
            throw new IllegalStateException("Internal error: Unexpected OWLException.",shouldntHappen);
        }
    }
    
    protected static <T> Set<T> createUnion(Set<T> set1,Set<T> set2) {
        Set<T> result=new HashSet<T>();
        result.addAll(set1);
        result.addAll(set2);
        return result;
    }
    
    protected static OWLObjectProperty getObjectProperty(OWLDataFactory factory,AtomicRole atomicRole) {
        return factory.getOWLObjectProperty(URI.create(atomicRole.getURI()));
    }
    
    protected static OWLObjectPropertyExpression getObjectPropertyExpression(OWLDataFactory factory,Role role) {
        if (role instanceof AtomicRole)
            return factory.getOWLObjectProperty(URI.create(((AtomicRole)role).getURI()));
        else {
            AtomicRole inverseOf=((InverseRole)role).getInverseOf();
            return factory.getOWLObjectProperty(URI.create(inverseOf.getURI())).getInverseProperty();
        }
    }
    
    
    // Loading and saving the Reasoner object

    public void save(File file) throws IOException {
        OutputStream outputStream=new BufferedOutputStream(new FileOutputStream(file));
        try {
            save(outputStream);
        }
        finally {
            outputStream.close();
        }
    }

    public void save(OutputStream outputStream) throws IOException {
        ObjectOutputStream objectOutputStream=new ObjectOutputStream(outputStream);
        objectOutputStream.writeObject(this);
        objectOutputStream.flush();
    }

    public static Reasoner loadReasoner(InputStream inputStream) throws IOException {
        try {
            ObjectInputStream objectInputStream=new ObjectInputStream(inputStream);
            return (Reasoner)objectInputStream.readObject();
        }
        catch (ClassNotFoundException e) {
            IOException error=new IOException();
            error.initCause(e);
            throw error;
        }
    }

    public static Reasoner loadReasoner(File file) throws IOException {
        InputStream inputStream=new BufferedInputStream(new FileInputStream(file));
        try {
            return loadReasoner(inputStream);
        }
        finally {
            inputStream.close();
        }
    }

    // Utilities for translating between hierarchy views:
    
    static class RoleToString implements Translator<AtomicRole,String> {
        public String translate(AtomicRole r) {
            return r.getURI();
        }
        public boolean equals(Object o) {
            return o instanceof ConceptToString;
        }
        public int hashCode() {
            return 0;
        }
    }

    static class ConceptToOWLClass implements Translator<AtomicConcept,OWLClass> {
        private OWLDataFactory factory;
        ConceptToOWLClass(OWLDataFactory factory) {
            this.factory=factory;
        }
        public OWLClass translate(AtomicConcept c) {
            return factory.getOWLClass(URI.create(c.getURI()));
        }
        public boolean equals(Object o) {
            return o instanceof ConceptToOWLClass;
        }
        public int hashCode() {
            return 0;
        }
    }

    static class RoleToOWLObjectProperty implements Translator<AtomicRole,OWLObjectProperty> {
        private OWLDataFactory factory;
        RoleToOWLObjectProperty(OWLDataFactory factory) {
            this.factory=factory;
        }
        public OWLObjectProperty translate(AtomicRole r) {
            // should really ensure that r is an object, not data, role
            return factory.getOWLObjectProperty(URI.create(r.getURI()));
        }
        public boolean equals(Object o) {
            return o instanceof RoleToOWLObjectProperty;
        }
        public int hashCode() {
            return 0;
        }
    }

    static class RoleToOWLDataProperty implements Translator<AtomicRole,OWLDataProperty> {
        private OWLDataFactory factory;
        RoleToOWLDataProperty(OWLDataFactory factory) {
            this.factory=factory;
        }
        public OWLDataProperty translate(AtomicRole r) {
            // should really ensure that r is a data, not object, role
            return factory.getOWLDataProperty(URI.create(r.getURI()));
        }
        public boolean equals(Object o) {
            return o instanceof RoleToOWLDataProperty;
        }
        public int hashCode() {
            return 0;
        }
    }

    static class IndividualToString implements Translator<Individual,String> {
        public String translate(Individual i) {
            return i.getURI();
        }
        public boolean equals(Object o) {
            return o instanceof IndividualToString;
        }
        public int hashCode() {
            return 0;
        }
    }

    static class StringToConcept implements Translator<Object,AtomicConcept> {
        public AtomicConcept translate(Object o) {
            return AtomicConcept.create(o.toString());
        }
        public boolean equals(Object o) {
            return o instanceof StringToConcept;
        }
        public int hashCode() {
            return 0;
        }
    }

    static class OWLClassToConcept implements Translator<Object,AtomicConcept> {
        public AtomicConcept translate(Object o) {
            return AtomicConcept.create(((OWLClass)o).getURI().toString());
        }
        public boolean equals(Object o) {
            return o instanceof OWLClassToConcept;
        }
        public int hashCode() {
            return 0;
        }
    }

    static class ConceptToString implements Translator<AtomicConcept,String> {
        public String translate(AtomicConcept c) {
            return c.getURI();
        }
        public boolean equals(Object o) {
            return o instanceof ConceptToString;
        }
        public int hashCode() {
            return 0;
        }
    }
}
