(ns persistent-data-structures.vector
  (:use [persistent-data-structures.utils :only [unsigned-bit-shift-right copy-array]])
  (:import [clojure.lang MapEntry Util]))

;; # Persistent Vector

;; This is an implementation of Clojure's persistent vector data
;; structure in pure Clojure, using only arrays.  It aims to be a
;; faithful porting of Rich's initial implementation from Java to
;; Clojure.

;; ## Why?

;; As Clojure gets ported to new backends such as Javascript and
;; Scheme, the persistent data structures that make Clojure such a joy
;; to use are generally not ported.  Thus, some assumptions about
;; running times become invalid.  It is generally easier to port the
;; array operations to a new backend, since nearly all languages have
;; arrays built in.

;; # The Implementation

;; ## The Node

;; A node is just an array of 32 objects.  They either point to other
;; nodes or contain the objects that are in the vector.

(deftype VectorNode [^objects array])

(def empty-node (VectorNode. (object-array 32)))

;; We begin with some helper functions.

(defn- array-for
  "A helper function that finds the array containing element `i` "
  [vec i]
  (let [cnt (.cnt vec)
        ^VectorNode root (.root vec)
        shift (.shift vec)
        ^objects tail (.tail vec)
        tailoff (if (< cnt 32) 0 (bit-shift-left (unsigned-bit-shift-right (dec cnt) 5) 5))]
     (if (and (>= i 0) (< i cnt))
       (if (>= i tailoff)
         tail
         (loop [^VectorNode node root level shift]
           (let [^objects arr (.array node)]
             (if (<= level 0)
               arr
               (let [new-node (aget arr (bit-and (unsigned-bit-shift-right i level) 0x01f))]
                 (recur new-node (- level 5)))))))
       (throw (IndexOutOfBoundsException.)))))


;; ## Chunked Sequences

(deftype ArrChunk [^objects array off end _meta]
  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this m] (ArrChunk. array off end m))
  clojure.lang.IChunk
  (nth [this i]
    (aget array (+ off i)))
  (nth [this i not-found]
    (if (and (>= i 0) (< i (.count this)))
      (.nth this i)
      not-found))
  (count [this]
    (- end off))
  (dropFirst [this]
    (if (= off end)
      (throw (IllegalStateException. "dropFirst of empty chunk"))
      (ArrChunk. array (inc off) end {})))
  (reduce [this f start]
    (reduce f start (drop off array))))

(deftype ChunkedVector [vec ^objects node i offset _meta]
  clojure.lang.IChunkedSeq
  (chunkedFirst [this] (ArrChunk. node offset (count node) {}))
  (chunkedNext [this]
    (when (< (+ i (count node)) (.count vec))
      (ChunkedVector. vec (array-for vec (+ i (count node))) (+ i (count node)) 0 _meta)))
  (chunkedMore [this]
    (if-let [s (.chunkedNext this)]
      s
      (list)))
  (first [this]
    (aget node offset))
  (next [this]
    (if (< (inc offset) (count node))
      (ChunkedVector. vec node i (inc offset) _meta)
      (.chunkedNext this)))
  clojure.lang.Seqable
  (seq [this] this)
  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this m]
    (ChunkedVector. vec node i offset m)))

;; ## The Vector

;; ### The persistent vector type.

;; As a data structure, it's pretty simple.  There is a tree structure
;; with a fan-out of 32 that is created by linking `VectorNode`s to
;; one another, and there is a `tail`, which is simply an array of
;; less than 32 elements that when full will be added to the tree
;; structure.

;; One benefit of having the fan-out be 32 (or any power of two
;; really) is that the `k`th element can be found easily using
;; bit-twiddling operations.  For the sake of example and to keep the
;; numbers small, let's imagine that the fan-out was 4, and that there
;; were 65 elements in the vector.  Then we would have the situation
;; where there is a tail with one element in it and a full tree that
;; is three levels high.  Let's try to find the 27th element.  The
;; number 27 is 011011 in binary.  We can figure out which sub-tree of
;; the root that the element is in by looking at sub-tree number
;; (010111 >> (2 * 2)) & 11 = 01 (where the numbers with only 1s and
;; 0s are in binary, >> denotes right-shift, and & denotes
;; bitwise-and).  We find the subtree of that tree containing the 27th
;; element by looking at sub-tree number (010111 >> (1 * 2)) & 11 =
;; 10, and finally we look at element number (010111 >> (0 * 2)) & 11
;; = 11 to find the element itself.

(deftype PVector [^int cnt ^int shift ^VectorNode root ^objects tail _meta]
  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this m]
    (PVector. cnt shift root tail m))
  
  clojure.lang.IPersistentVector
  (length [this] cnt)

  ;; Change the `i`th value in the vector to `val`.
  
  (assocN [this i val]
    (let [tailoff (if (< cnt 32) 0 (bit-shift-left (unsigned-bit-shift-right (dec cnt) 5) 5))]
     (cond (and (>= i 0) (< i cnt))
           (if (>= i tailoff)
             (let [^objects new-tail (object-array (count tail))
                   _ (copy-array tail new-tail)
                   _ (aset new-tail (bit-and i 0x1f) val)]
               (PVector. cnt shift root new-tail _meta))
             (let [do-assoc (fn do-assoc [level node i val]
                              (let [node-array (.array node)
                                    new-array (object-array (count node-array))
                                    _ (copy-array node-array new-array)
                                    new-node (VectorNode. new-array)]
                                (if (= level 0)
                                  (do (aset new-array (bit-and i 0x01f) val)
                                      new-node)
                                  (let [subidx (bit-and (unsigned-bit-shift-right i level) 0x01f)]
                                    (aset new-array subidx (do-assoc (- level 5) (aget node-array subidx) i val))
                                    new-node))))]
               (PVector. cnt shift (do-assoc shift root i val) tail _meta)))
           (= i cnt)
           (.cons this val)
           :else
           (throw (IndexOutOfBoundsException.)))))

  ;; Add an element to the end of the vector.
  
  (cons [this o]
    (let [tailoff (if (< cnt 32) 0 (bit-shift-left (unsigned-bit-shift-right (dec cnt) 5) 5))]
      (if (< (- cnt tailoff) 32)
       (let [tail-count (count tail)
             ^objects new-tail (object-array (inc tail-count))
             _ (copy-array tail new-tail)
             _ (aset new-tail tail-count o)]
         (PVector. (inc cnt) shift root new-tail _meta))
       (let [tail-node (VectorNode. tail)
             overflow-root? (> (unsigned-bit-shift-right cnt 5) (bit-shift-left 1 shift))
             new-path (fn new-path [level node]
                        (if (= level 0)
                          node
                          (let [^objects new-array (object-array 32)
                                ret (VectorNode. new-array)
                                _ (aset new-array 0 (new-path (- level 5) node))]
                            ret)))
             push-tail (fn push-tail [level parent tail-node]
                         (let [subidx (bit-and (unsigned-bit-shift-right (dec cnt) level) 0x01f)
                               ^objects parent-array (.array parent)
                               ^objects new-arr (object-array (count parent-array))
                               _ (copy-array parent-array new-arr)
                               ret (VectorNode. new-arr)
                               node-to-insert (if (= level 5)
                                                tail-node
                                                (let [child (aget parent-array subidx)]
                                                  (if child
                                                    (push-tail (- level 5) child tail-node)
                                                    (new-path (- level 5) tail-node))))
                               _ (aset new-arr subidx node-to-insert)]
                           ret))

             [new-shift new-root]
             (if overflow-root?
               (let [^objects new-root-array (object-array 32)
                     _ (aset new-root-array 0 root)
                     _ (aset new-root-array 1 (new-path shift tail-node))]
                 [(+ shift 5) (VectorNode. new-root-array)])
               [shift (push-tail shift root tail-node)])]
         (PVector. (inc cnt) new-shift new-root (to-array (list o)) _meta)))))
  
  clojure.lang.IPersistentCollection
  (empty [this]
    (PVector. 0 5 empty-node (to-array '()) _meta))

  ;; Check whether another sequence has all the same elements as this
  ;; vector.
  
  (equiv [this o]
    (if (or (list? o) (vector? o))
      (if (not= (count o) (.count this))
        false
        (every? (map = o (.seq this))))
      (if (not (sequential? o))
        false
        (loop [s (.seq this) a (seq o)]
          (cond (and (nil? s) (nil? a))
                true
                (nil? s)
                false
                (nil? a)
                false
                (not= (first s) (first a))
                false
                :else
                (recur (rest s) (rest a)))))))

  clojure.lang.Associative

  (assoc [this key val]
    (if (integer? key)
      (.assocN this key val)
      (throw (IllegalArgumentException. "Key must be integer"))))

  (entryAt [this key]
    (when (and (integer? key) (>= key 0) (< key cnt))
      (MapEntry. key (.nth this key))))

  (containsKey [this key]
    (and (integer? key) (>= key 0) (< key cnt)))
  
  clojure.lang.IPersistentStack

  ;; Return the last element of the vector
  
  (peek [this]
    (if (> (.count this) 0)
      (.nth this (dec cnt))))

  ;; Return the vector without its last element.
  ;; Not yet implemented.

  (pop [this]
    (throw (UnsupportedOperationException.)))
  
  clojure.lang.Seqable
  (seq [this]
    (ChunkedVector. this (array-for this 0) 0 0 {}))
  
  clojure.lang.Reversible
  (rseq [this]
    (throw (UnsupportedOperationException.)))
  
  clojure.lang.IFn
  (invoke [this k] (.nth this k))
  (invoke [this k not-found] (.nth this k not-found))
  
  clojure.lang.Indexed
  (nth [this ^int i]
    (let [^objects node (array-for this i)]
      (aget node (bit-and i 0x01f))))
  (nth [this i not-found]
    (if (and (>= i 0) (< i cnt))
      not-found
      (.nth this i)))

  clojure.lang.IHashEq
  (hasheq [this]
    (reduce #(+ (* 31 %) (Util/hasheq %2))))
  
  clojure.lang.Counted
  (count [this]
    cnt))

;; ### Creating the persistent vector

;; The naive way of constructing a persistent vector from a collection
;; is to repeatedly `conj` elements of the collection onto the empty
;; vector.  Though this works, it is slow for a couple of reasons.
;; First, it creates a lot of extra objects to be GC'd without a lot
;; of purpose.  Second, it takes O(n log n) time (where the base of
;; the log is 32, so the log n factor will always be pretty small, but
;; still) rather than the O(n) time that is both optimal and possible.

;; The algorithm works from the bottom up by repeatedly partitioning
;; the input into groups of 32.  Since the size of the input at each
;; step is a constant fraction of the previous size, and a linear
;; amount of work is done at each step, this is a linear-time
;; algorithm.

(defn pvec
  "Construct a PVector from the collection `coll` in linear time."
  [coll]
  (let [reversed-partition (fn reversed-partition [n coll]
                             (loop [ret () co coll remaining (count coll)]
                               (if (empty? co)
                                 ret
                                 (let [rem (min 32 remaining)
                                       ^objects ret-array (object-array rem)
                                       next-co (loop [cnt 0 coll co]
                                                 (if (= cnt rem)
                                                   coll
                                                   (do (aset ret-array cnt (first coll))
                                                       (recur (inc cnt) (rest coll)))))]
                                  (recur (cons ret-array ret) next-co (- remaining rem))))))
        grouped-coll (reversed-partition 32 coll)
        big-groups (rest grouped-coll)
        tail (first grouped-coll)
        reversed-map (fn [f coll]
                       (loop [ret () coll coll]
                         (if (empty? coll)
                           ret
                           (recur (cons (f (first coll)) ret) (rest coll)))))
        c (+ (* 32 (dec (count grouped-coll))) (count tail))
        shift (loop [level 0 c (unsigned-bit-shift-right c 5)]
                 (if (<= c 32)
                   (* 5 (inc level))
                   (recur (inc level) (bit-shift-right c 5))))
        root (loop [groups big-groups level shift]
               (let [vector-nodes (reversed-map #(VectorNode. %) groups)]
                 (if (= level 5)
                   (VectorNode. (to-array vector-nodes))
                   (recur (reversed-partition 32 vector-nodes) (- level 5)))))]
    (PVector. c shift root tail {})))

(defn empty-pvector
  "Create an empty PVector"
  []
  (PVector. 0 5 empty-node (to-array '()) {}))


(comment
  (time
   (dotimes [n 100]
     (count (range 10000))))

  (pvec (range 38))
  (rem 100 32)

  (def m (empty-pvector))
  (sequential? m)
  (def o (-> m (conj 1) (conj 2)))
  (def p (reduce conj m (range 1025)))
  (time
   (dotimes [n 100]
     (reduce conj m (range 1025))))
  (let [q (apply list (range (* 32 32 32)))]
   (time
    (dotimes [n 100]
      (vec q))))
  (let [q (apply list (range (* 32 32 32)))]
   (time
    (dotimes [n 100]
      (pvec q))))
  (time
   (dotimes [n 100]
    (nth p 1023)))
  (def q (vec (range 1025)))
  (time
   (dotimes [n 100]
     (nth q 1023)))
  (pvec (range (* 3 1024)))
  (def r (pvec (range 1025)))
  (r 65)
  (def s (vec (range 1025)))
  ((assoc q 11 12) 11)
  (q 11)
  ((assoc p 1023 12) 11)

  )