import N6.SparseProductReduceCore
import review.SparseCheck

namespace N6.SparseProductReduce
open N6.SparseCheck N6.KroneckerCheck

variable {R : Type*} [CommRing R] (x : Fin 5 → R)

theorem value_reduceProducts (ps : Products) :
    value x (reduceProducts ps) = pairs (value x) ps := by
  induction ps with
  | nil => rfl
  | cons z ps ih =>
    simp only [reduceProducts, value_merge, value_mul, pairs, ih]

theorem pairs_vanish (ps : Products) (h : zero (reduceProducts ps) = true) :
    pairs (value x) ps = 0 := by
  exact (value_reduceProducts x ps).symm.trans (value_zero x h)

end N6.SparseProductReduce
