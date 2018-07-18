(ns modelmeth.ontolatex
  "Management of OWL files"
  {:author "Peter Denno"}
  (:require [clojure.pprint :refer (cl-format pprint)]
            [clojure.walk :refer-only (prewalk prewalk-demo)]
            [clojure.zip :as zip]
            [tawny.owl :as owl]
            [tawny.query :as query]
            [tawny.render]
            [tawny.read :as rowl]
            [tawny.lookup :as look])
  (:use clojure.java.io)
  (:import
   (org.semanticweb.owlapi.model
    HasIRI
    OWLAxiom
    OWLEntity
    OWLObject
    OWLOntologyManager OWLOntology IRI
    OWLClassExpression OWLClass OWLAnnotation
    OWLDataProperty OWLObjectProperty
    OWLDataPropertyExpression ; not useful?
    OWLIndividual OWLDatatype
    OWLObjectPropertyExpression
    OWLNamedObject OWLOntologyID)
   [org.semanticweb.owlapi.search EntitySearcher]))

;;; Meaning of some variables use in functions:
;;;  obj - a OWLAPI object, one of OWLObject, OWLDataProperty, OWLObjectProperty
;;;  tmap - a hash-map of information collected from obj through the thing-map function.


(def ^:private diag (atom nil))

(def +params+ (atom {:section-offset 1
                     :onto-namespace 'onto}))

(def tawny-types [:tawny.owl/class :tawny.owl/individual :tawny.owl/property
                  :tawny.owl/object-property :tawny.owl/data-property])

(def ontologies "A list of the ontologies used in this project"
  ["http://modelmeth.nist.gov/ontologies/pizza/pizza.owl"
   "http://www.linkedmodel.org/schema/dtype"
   "http://www.linkedmodel.org/schema/vaem"
   "http://qudt.org/2.0/schema/qudt"
   "http://modelmeth.nist.gov/modeling"
   "http://modelmeth.nist.gov/operations"])

;;; POD I expected this to be http://modelmeth.nist.gov/modeling#clojureCodeNote
(def ^:const code-iri "Used to identify clojure notes from thing-mapped objects."
  (list :iri "http://modelmeth.nist.gov/modeling#clojureCode"))

#_(def manager (owl/owl-ontology-manager))

(defn clear-ontos!
  "Remove all the ontologies"
  []
  (repeatedly
   5
   (fn []           
     (doall (map #(owl/remove-ontology-maybe (OWLOntologyID. (owl/iri %))) ontologies)))))

(defn simplify-tawny-annotations
  "Some are (:comment <pairs>). Some are (:annotation code-iri <pairs>)"
  [tawny-notes]
  (vec
   (doall
    (map #(let [original %]
            (as-> original ?note
              (cond (= (first ?note) :comment) (second ?note),
                    (= (first ?note) :annotation ) (-> ?note rest rest first))
              (apply hash-map ?note)
              (assoc ?note :otype (first original))))
         tawny-notes))))

(defn short-name
  "Argument is an OWLClassImpl etc."
  [obj]
  (->> obj
       look/named-entity-as-string
       (re-matches #".*\#(.*)")
       second))

(defn properties-of
  "Return a seq of properties that are relevant to the argument tmap."
  [tmap property-map]
  (let [sname (:short-name tmap)]
     (filter (fn [pm] (or (some #(= sname %) (:domains pm))
                          (some #(= sname %) (:ranges  pm))))
             (vals property-map))))

(defn thing-map
  "Return a map of information about the class. See also query/into-map-with"
  ([obj] (thing-map obj {})) ; Used by ignore? 
  ([obj property-map]
   (when (instance? OWLClass obj)
     (let [sname (short-name obj)]
       (as-> (apply hash-map (tawny.render/as-form obj :keyword true)) ?map
         (assoc ?map :short-name sname) ; POD (or label)
         (assoc ?map :var (intern (:onto-namespace @+params+) (symbol sname)))
         (assoc ?map :notes (simplify-tawny-annotations (:annotation ?map)))
         (assoc ?map :subclass-of (doall (map short-name ; POD there are other ways. See notes 2017-07-22. 
                                              (filter #(instance? OWLClass %)
                                                      (owl/direct-superclasses obj)))))
         (assoc ?map :properties (properties-of ?map property-map)))))))

(defn clojure-code
  "Return any http://modelmeth.nist.gov/modeling#clojureCode annotation"
  [obj]
  (some #(when (and (= (:otype %) :annotation)
                    (= (:type %) code-iri))
           (:literal %))
        (-> obj thing-map :notes)))

;;; POD needs to return true if a supertype is ignored. 
(defn ignore?
  "Returns true if the tawny thing has a clojure {:priority :ignore}"
  [obj]
  (if (some #(= (owl/guess-type (owl/get-current-ontology) obj) %) tawny-types)
    (when-let [code (clojure-code obj)]
      (= :ignore (:priority (read-string code))))
    true))

(defn onto-parent-child-map
  "Define the parent/child relationship as a map."
  [root]
  (let [obj2var-map
        (let [ks (remove #(ignore? (var-get %))
                         (vals (ns-interns (:onto-namespace @+params+))))
              vs (map var-get ks)]
          (clojure.set/map-invert (zipmap ks vs))),
        m (reduce (fn [index node]
                    (assoc index (get obj2var-map node)
                           (map #(get obj2var-map %)
                                (owl/direct-subclasses node))))
                  {}
                  (conj (owl/subclasses root) root))]
    (as-> m ?map
      (dissoc ?map nil)
      (reduce (fn [m k] (update m k #(vec (filter identity %))))
              ?map
              (keys ?map)))))

(defn next-paths
  "Return all paths one-step further than the argument, if any."
  [path index]
  (if (empty? path)
    []
    (vec (map #(conj path %) (vec (get index (last path)))))))

(defn onto-root-map
  "Define the ontology root structure as a nested map."
  [accum paths index]
  (if (empty? paths)
    accum
    (recur
     (assoc-in accum (first paths) {})
     (let [nexts (next-paths (first paths) index)]
       (if (empty? nexts)
         (vec (next paths))
         (into nexts (vec (next paths)))))
     index)))

(defn vectify
  "Turn a nested map like that from onto-root-map into a nested vector
   where every var leaf is followed by a vector representing its subclasses 
   (could be empty)."
  [nested-map]
  (clojure.walk/prewalk
   #(if (var? %)
      %
      (vec (interleave (keys %) (vals %))))
   nested-map))

;;;============== Rendering ===============================================
(defn zip-depth
  "Return the depth of the location."
  [loc]
  (loop [loc loc
         depth 0]
    (if (not (zip/up loc))
      depth
      (recur (zip/up loc) (inc depth)))))

;;; I expand the tree with leaf-node maps before navigation and printing
;;; because this is the place to calculate :depth.
(defn onto-leaf-nodes
  "Return the onto vector structure with thing-maps replacing vars."
  [onto-vec property-map]
  (loop [loc (-> onto-vec zip/vector-zip zip/down)]
    (as-> loc ?loc
      (if (var? (zip/node ?loc))
        (zip/edit ?loc #(-> (thing-map (var-get %) property-map) ; POD why dec below?
                            (assoc :depth (dec (+ (:section-offset @+params+)
                                                  (zip-depth ?loc))))))
        ?loc)
      (zip/next ?loc)
      (if (zip/end? ?loc)
        (zip/root ?loc)
        (recur ?loc)))))

(defn subsub [n]
  (cond 
    (= n 0) "\\section"
    (= n 1) "\\subsection"
    (= n 2) "\\subsubsection"
    (= n 3) "\\paragraph"
    (= n 4) "\\subparagraph"
    :else ""))

(defn entity-comment [tmap]
  (some #(when (= (:otype %) :comment) (:literal %))
        (:notes tmap)))

;;; write-superclasses:  "Write text describing subtyping relationships."
(defn- write-superclasses-dispatch [tmap form] form)
(defmulti write-superclasses #'write-superclasses-dispatch)

;;; POD Needs work. Doesn't yet describe disjoint / disjoint exhaustive.
(defmethod write-superclasses :latex [tmap form]
  (let [sname (:short-name tmap)
        stypes (:subclass-of tmap)]
    (doall
     (map #(println (cl-format nil "\\\\$ ~A \\sqsubseteq ~A$" %1 %2))
          (repeat (count stypes) sname)
          stypes))))

(defmethod write-superclasses :csv [tmap form]
  (let [sname (:short-name tmap)
        stypes (:subclass-of tmap)]
    (print (cl-format nil "~{~A~^, ~} |" stypes))))

;;;  "Write text describing properties the class is involved in."
(defn- write-properties-dispatch [tmap form] form)
(defmulti write-properties #'write-properties-dispatch)

;;; POD Should this just look at direct properties? 
(defmethod write-properties :latex
  [tmap form]
  (let [sname (:short-name tmap)]
    (doall
     (map (fn [rel]
            (if (some #(= sname %) (:domains rel))
              (println (cl-format nil "\\\\$\\: ~A\\: \\textbf{~A}\\: ~{~A~^\\: \\vee~}\\: ~A$"
                                  sname
                                  (short-name (:obj rel))
                                  (:ranges rel)
                                  (:characteristics rel)))
              (println (cl-format nil "\\\\$\\: ~{~A~^\\: \\vee~}\\: \\textbf{~A}\\: ~A\\:  ~A$"
                                  (:domains rel)
                                  (short-name (:obj rel))
                                  sname
                                  (:characteristics rel)))))
          (:properties tmap)))
    #_(println "\\\\")))

(defmethod write-properties :csv
  [tmap form]
  (let [sname (:short-name tmap)]
    (print (cl-format nil "| ~A" sname))))

(defn- write-concept-dispatch [tmap form] form)
(defmulti write-concept #'write-concept-dispatch)

;;;   "Write text about concept."
(defmethod write-concept :latex
  [tmap form]
  (let [sname (:short-name tmap)
        comment (entity-comment tmap)]
    (println (cl-format nil "\\\\\\\\   \\textbf{~A}\\\\Description: ~A\\\\"
                        sname (or comment "+++Needs Definition+++")))
    (write-superclasses tmap form)
    (write-properties tmap form)))

(defmethod write-concept :csv
  [tmap form]
  (let [sname (:short-name tmap)
        comment (entity-comment tmap)]
    (println (cl-format nil " ~A | ~A " sname (or comment "+++Needs Definition+++")))
    (write-superclasses tmap form)
    #_(write-properties tmap form)))

(defn- heading-dispatch [section form] form)
(defmulti write-section-heading #'heading-dispatch)

(defmethod write-section-heading :latex 
  [section form]
  (println (cl-format nil "~A{~A}\\\\" (subsub (:depth section)) (:short-name section)))
  (println (cl-format nil "Description: ~A\\\\" (or (entity-comment section) "+++Needs Definition+++")))
  (write-superclasses section :latex)
  (write-properties section :latex))

(defmethod write-section-heading :csv 
  [section form]
  #_(write-superclasses section :csv)
  #_(write-properties section :csv))

;;; POD Doesn't clojure have something like this?
(defn by-n
  "Return the argument chopped up into n-sized sub-seqs"
  [n a-seq]
  (loop [s a-seq
         result []]
    (if (empty? s) 
      result
      (recur (drop n s) (conj result (take n s))))))

(defn partition-concepts
  "Argument is a loc that names a section. Return a map f associated nodes (thing-maps)
   including the :section tmap, :direct-concepts thing-maps and :subsections thing-maps."
  [loc]
  (let [children (by-n 2 (-> loc zip/next zip/node))]
    {:section (-> loc zip/node)
     :direct-concepts (map first (filter #(-> % second empty?) children))
     :subsections     (map vec   (remove #(-> % second empty?) children))}))

(defn write-section!
  "Write a \\section, \\subsection etc. Calls itself recursively on zip/children."
  [loc form]
  (cond (empty? loc) nil,
        (map? loc) (throw (ex-info "map?" {}))
        (var? loc) (throw (ex-info "var?" {}))
        (zip/end? loc) nil,
        ;;(-> loc zip/next zip/branch?)
        (-> loc zip/node map?)
        (let [parts (partition-concepts loc)
              section (:section parts)
              concepts (:direct-concepts parts)
              subsections (:subsections parts)]
          (when section (write-section-heading section form))
          (doall (map #(write-concept % form) concepts))
          (doall (map #(write-section! (-> % zip/vector-zip zip/down) form) subsections)))))

(defn write-onto-nodes!
  "Write latex for the onto-root structure"
  [v property-map form]
  (-> v 
      (onto-leaf-nodes property-map)
      zip/vector-zip
      zip/down
      (write-section! form)))

;;; POD onto.??? parameterize 
(defn read-base-ontos!
  []
  (rowl/read :iri "http://www.linkedmodel.org/schema/dtype"
             :namespace (create-ns 'onto) ; was onto.dtype
             :location (clojure.java.io/file "resources/dtype.owl"))
  (rowl/read :iri "http://www.linkedmodel.org/schema/vaem"
             :namespace (create-ns 'onto) ; was onto.vaem
             :location (clojure.java.io/file "resources/vaem.owl"))
  (rowl/read :iri "http://qudt.org/2.0/schema/qudt"
             :namespace (create-ns 'onto) ; was onto.qudt
             :location (clojure.java.io/file "resources/SCHEMA_QUDT-v2.0.ttl")))

(defn property-characteristics
  "Return a vector containing keywords indicating which of the 7 OWL property
   characteristics are true for the argument property."
  [p ont]
  (if (instance? OWLDataProperty p)
    (cond-> []
      (EntitySearcher/isFunctional p ont)        (conj :functional))
    (cond-> []
      (EntitySearcher/isTransitive p ont)        (conj :transitive)
      (EntitySearcher/isFunctional p ont)        (conj :functional)
      (EntitySearcher/isInverseFunctional p ont) (conj :inverse-functional)
      (EntitySearcher/isSymmetric p ont)         (conj :symmetric)
      (EntitySearcher/isAsymmetric p ont)        (conj :asymmetric)
      (EntitySearcher/isIrreflexive p ont)       (conj :irreflexive)
      (EntitySearcher/isReflexive p ont)         (conj :reflexive))))

(defn property-analysis
  "Return a map indexed by tawny vars. Entries are maps describing onto properties."
  []
  (let [o (owl/get-current-ontology)
        prop-vars
        (filter #(or (instance? OWLDataProperty (var-get %))
                     (instance? OWLObjectProperty (var-get %)))
                (vals (ns-interns (:onto-namespace @+params+))))]
    (reduce (fn [prop-map var] ; Key var already exists. I use sname to find it. 
              (let [obj (var-get var)]
                (-> prop-map
                    (assoc var {})
                    (assoc-in [var :obj] obj)
                    (assoc-in [var :var] var)
                    (assoc-in [var :obj?] (instance? OWLObjectProperty obj))
                    (assoc-in [var :domains] (map short-name (EntitySearcher/getDomains obj o)))
                    (assoc-in [var :ranges]  (map short-name (EntitySearcher/getRanges  obj o)))
                    (assoc-in [var :characteristics] (property-characteristics obj o)))))
            {} prop-vars)))
                    
(defn write-onto!
  [onto-file out-file uri-base form & root-concepts] ; This interns vars, including root-concepts.
  (clear-ontos!)
  (read-base-ontos!)
  (rowl/read :iri (str "http://modelmeth.nist.gov/" uri-base)
             :namespace (create-ns (:onto-namespace @+params+)) 
             :location (clojure.java.io/file onto-file))
  (with-open [wrtr (writer out-file)]
    (binding [*out* wrtr]
      (when (= form :csv)
        (println "Superclasses | Term | Description"))
      (let [property-map (property-analysis)]
        (doall (map (fn [root-sym]
                      (let [pc-map (onto-parent-child-map (var-get (resolve root-sym)))]
                        (-> (onto-root-map {} [[(resolve root-sym)]] pc-map) 
                            vectify 
                            (write-onto-nodes! property-map form))))
                    root-concepts))))))

(defn ops []
  (write-onto!
   "resources/operations.ttl"
   ;;"/Users/pdenno/TwoDrive/OneDrive/Repo/Loughborough/Writing/Papers/MAPPING/operations-ontology.tex"
   "./output/operations-ontology.tex"
   "ops"
   :latex
   'onto/OperationsDomainConcept))

(defn ops-csv []
  (write-onto!
   "resources/operations.ttl"
   "./output/operations-ontology.csv"
   "ops"
   :csv
   'onto/OperationsDomainConcept))


(defn modi []
  (write-onto!
   "resources/modeling.ttl"
   ;;"/Users/pdenno/TwoDrive/OneDrive/Repo/Loughborough/Writing/Papers/MAPPING/modeling-ontology.tex"
   "./output/modeling-ontology.tex"
   "modeling"
   :latex
   'onto/Abstract
   'onto/Physical))

(defn modi-csv []
  (write-onto!
   "resources/modeling.ttl"
   ;;"/Users/pdenno/TwoDrive/OneDrive/Repo/Loughborough/Writing/Papers/MAPPING/modeling-ontology.tex"
   "./output/modeling-ontology.tex"
   "modeling"
   :csv
   'onto/Abstract
   'onto/Physical))


(defn ppp []
  (binding [clojure.pprint/*print-right-margin* 140]
    (pprint *1)))

(defn ppprint [arg]
  (binding [clojure.pprint/*print-right-margin* 140]
    (pprint arg)))
