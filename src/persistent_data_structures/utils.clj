(ns persistent-data-structures.utils)

(defn unsigned-bit-shift-right
  "Shifts the input `x` to the right by `n` places and sets the leftmost bit to 0."
  [^long x ^long n]
  (bit-and 0xefffffff (bit-shift-right x n)))

(defn copy-array
  "Copy the elements in `from-array` to `to-array`.  Assumes that
   `to-array` is as long as `from-array`."
  [^objects from-array ^objects to-array]
  (loop [c (count from-array)]
    (when (> c 0)
      (aset to-array (dec c) (aget from-array (dec c)))
      (recur (dec c))))
  to-array)

