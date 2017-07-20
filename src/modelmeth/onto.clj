(ns modelmeth.onto
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
    OWLIndividual OWLDatatype
    OWLObjectPropertyExpression
    OWLNamedObject OWLOntologyID)
   [org.semanticweb.owlapi.search EntitySearcher]))

(def diag (atom nil))

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
     (map #(owl/remove-ontology-maybe (OWLOntologyID. (owl/iri %))) ontologies))))

(defn simplify-tawny-annotations
  "Some are (:comment <pairs>). Some are (:annotation code-iri <pairs>)"
  [tawny-notes]
  (vec
   (map #(let [original %]
           (as-> original ?note
               (cond (= (first ?note) :comment) (second ?note),
                     (= (first ?note) :annotation ) (-> ?note rest rest first))
               (apply hash-map ?note)
               (assoc ?note :otype (first original))))
        tawny-notes)))

(defn short-name [node]
  (->> node
       look/named-entity-as-string
       (re-matches #".*\#(.*)")
       second))

(defn thing-map
  "Return a map of information about the class. See also query/into-map-with"
  [thing]
  (let [sname (short-name thing)]
    (as-> (apply hash-map (tawny.render/as-form thing :keyword true)) ?map
      (assoc ?map :short-name sname) ; POD (or label)
      (assoc ?map :var (intern (:onto-namespace @+params+) (symbol sname)))
      (assoc ?map :notes (simplify-tawny-annotations (:annotation ?map))))))

(defn clojure-code
  "Return any http://modelmeth.nist.gov/modeling#clojureCode annotation"
  [thing]
  (some #(when (and (= (:otype %) :annotation)
                    (= (:type %) code-iri))
           (:literal %))
        (-> thing thing-map :notes)))

;;; POD needs to return true if a supertype is ignored. 
(defn ignore?
  "Returns true if the tawny thing has a clojure {:priority :ignore}"
  [thing]
  (if (some #(= (owl/guess-type (owl/get-current-ontology) thing) %) tawny-types)
    (when-let [code (clojure-code thing)]
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
  (reset! diag nested-map)
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
(defn latex-leaf-nodes
  "Return the onto vector structure with thing-maps replacing vars."
  [onto-vec]
  (loop [loc (-> onto-vec zip/vector-zip zip/down)]
    (as-> loc ?loc
      (if (var? (zip/node ?loc))
        (zip/edit ?loc #(-> (thing-map (var-get %)) ; POD why dec below?
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

(defn write-concepts [tmap-list]
  (when tmap-list
    (println "\n\\begin{description}")
    (doall 
     (map #(println (cl-format nil "   \\item[~A]: ~A"
                               (:short-name %) (or (entity-comment %) "+++Needs Definition+++")))
          tmap-list))
    (println "\\end{description}\n")))
  
(defn write-section-heading
  [section]
  (println (cl-format nil "~A{~A}" (subsub (:depth section)) (:short-name section)))
  (println (cl-format nil " ~A" (or (entity-comment section) "+++Needs Definition+++"))))

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
  "Sort concepts (thing-maps) before branches. Argument is a loc that names a section"
  [loc]
  (let [children (by-n 2 (-> loc zip/next zip/node))]
    {:section (-> loc zip/node)
     :direct-concepts (map first (filter #(-> % second empty?) children))
     :subsections     (map vec   (remove #(-> % second empty?) children))}))

(defn write-section!
  "Write a \\section, \\subsection etc. Calls itself recursively on zip/children."
  [loc]
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
          (when section (write-section-heading section))
          (write-concepts concepts)
          (doall (map #(write-section! (-> % zip/vector-zip zip/down)) subsections)))))

(defn latex-write-onto-nodes!
  "Write latex for the onto-root structure"
  [v]
  (-> v
      latex-leaf-nodes
      zip/vector-zip
      zip/down
      write-section!))

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

(defn latex-write-onto!
  [onto-file out-file uri-base & root-concepts] ; This interns vars, including root-concepts.
  (clear-ontos!)
  (read-base-ontos!)
  (rowl/read :iri (str "http://modelmeth.nist.gov/" uri-base)
             :namespace (create-ns (:onto-namespace @+params+)) 
             :location (clojure.java.io/file onto-file))
  (with-open [wrtr (writer out-file)]
    (binding [*out* wrtr]
      (doall (map (fn [root-sym]
                    (let [pc-map (onto-parent-child-map (var-get (resolve root-sym)))]
                      (-> (onto-root-map {} [[(resolve root-sym)]] pc-map)
                          vectify
                          latex-write-onto-nodes!)))
                  root-concepts)))))

(defn ops []
  (latex-write-onto!
   "resources/operations.ttl"
   "/Users/pdenno/TwoDrive/OneDrive/Repo/Loughborough/Writing/Papers/MAPPING/operations-ontology.tex"
   "ops"
   'onto/Operations))

(defn modi []
  (latex-write-onto!
   "resources/modeling.ttl"
   "/Users/pdenno/TwoDrive/OneDrive/Repo/Loughborough/Writing/Papers/MAPPING/modeling-ontology.tex"
   "modeling"
   'onto/Abstract
   'onto/Physical))

(defn ppp []
  (binding [clojure.pprint/*print-right-margin* 140]
    (pprint *1)))

(defn ppprint [arg]
  (binding [clojure.pprint/*print-right-margin* 140]
    (pprint arg)))
