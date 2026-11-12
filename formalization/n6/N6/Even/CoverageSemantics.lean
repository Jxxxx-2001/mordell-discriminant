import N6.Even.CoverageGround
import N6.Certificate
import review.SparseProductReduce

set_option maxRecDepth 32000
set_option maxHeartbeats 3000000

namespace N6.Even
open N6.SparseCheck N6.KroneckerCheck

theorem value_scalar {R : Type*} [CommRing R] (x : Fin 5 → R) (z : Int) :
    value x (scalar z) = (z : R) := by simp [scalar, value, monVal]

theorem EvenF_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hE1 : value x E1Data = 0)
    (hS : value x SData = 0)
    : value x EvenFData = 0 := by
  apply N6.Certificate.int_scaled_zero EvenFScale EvenFScale_ne_zero
  have h := N6.SparseProductReduce.pairs_vanish x EvenFPairs EvenFChecked
  simpa only [EvenFPairs, pairs, value_scalar, hE1, hS, mul_zero, add_zero] using h

theorem EvenG_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hE3 : value x E3Data = 0)
    : value x EvenGData = 0 := by
  apply N6.Certificate.int_scaled_zero EvenGScale EvenGScale_ne_zero
  have h := N6.SparseProductReduce.pairs_vanish x EvenGPairs EvenGChecked
  simpa only [EvenGPairs, pairs, value_scalar, hE3, mul_zero, add_zero] using h

theorem EvenP6_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hEvenF : value x EvenFData = 0)
    (hEvenG : value x EvenGData = 0)
    (hS : value x SData = 0)
    : value x EvenP6Data = 0 := by
  apply N6.Certificate.int_scaled_zero EvenP6Scale EvenP6Scale_ne_zero
  have h := N6.SparseProductReduce.pairs_vanish x EvenP6Pairs EvenP6Checked
  simpa only [EvenP6Pairs, pairs, value_scalar, hEvenF, hEvenG, hS, mul_zero, add_zero] using h

theorem EvenEGraph_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hEvenF : value x EvenFData = 0)
    (hEvenG : value x EvenGData = 0)
    (hS : value x SData = 0)
    : value x EvenEGraphData = 0 := by
  apply N6.Certificate.int_scaled_zero EvenEGraphScale EvenEGraphScale_ne_zero
  have h := N6.SparseProductReduce.pairs_vanish x EvenEGraphPairs EvenEGraphChecked
  simpa only [EvenEGraphPairs, pairs, value_scalar, hEvenF, hEvenG, hS, mul_zero, add_zero] using h

theorem coverage_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h1 : value x E1Data = 0) (h3 : value x E3Data = 0) (hs : value x SData = 0) :
    value x EvenP6Data = 0 ∧ value x EvenEGraphData = 0 := by
  have hf := EvenF_vanish x h1 hs
  have hg := EvenG_vanish x h3
  exact ⟨EvenP6_vanish x hf hg hs, EvenEGraph_vanish x hf hg hs⟩

#print axioms coverage_vanish
end N6.Even
