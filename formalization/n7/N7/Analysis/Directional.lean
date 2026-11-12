-- Adapted from the checked N6 analytic argument; see analysis/adapt_maximum.py.
import N7.Analysis.Stationarity
import N6.Analysis.Directional
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

namespace N7.Analysis

noncomputable def motion (z h : Configuration) (t : ℝ) : Configuration :=
  fun i => z i + (t : ℂ) * h i

noncomputable def pairSum (z h : Configuration) : ℂ :=
  ∑ p ∈ pairs, (h p.1 - h p.2) / (z p.1 - z p.2)

noncomputable def innerMoment (z h : Configuration) : ℂ := ∑ i, star (z i) * h i

theorem hasDerivAt_normSum_motion (z h : Configuration) :
    HasDerivAt (fun t => normSum (motion z h t)) (2 * (innerMoment z h).re) 0 := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => N6.hasDerivAt_normSq_motion (z i) (h i))
  convert hd using 1
  simp [innerMoment, Complex.mul_re, ← Finset.mul_sum]

theorem hasDerivAt_discriminant_motion (z h : Configuration) :
    HasDerivAt (fun t => discriminant (motion z h t))
      (discriminant z * (2 * (pairSum z h).re)) 0 := by
  let f := fun p : Fin 7 × Fin 7 => fun t : ℝ =>
    Complex.normSq ((z p.1 - z p.2) + (t : ℂ) * (h p.1 - h p.2))
  let r := fun p : Fin 7 × Fin 7 =>
    2 * ((h p.1 - h p.2) / (z p.1 - z p.2)).re
  have hd := N6.hasDerivAt_relative_product pairs f r (by
    intro p _
    convert N6.hasDerivAt_normSq_motion (z p.1 - z p.2) (h p.1 - h p.2) using 1
    simp only [f, r, Complex.ofReal_zero, zero_mul, add_zero]
    exact (N6.normSq_relative_derivative _ _).symm)
  convert hd using 1
  · funext t
    apply Finset.prod_congr rfl
    intro p _
    congr 1
    dsimp [motion]
    ring
  · simp [f, r, discriminant, pairSum, ← Finset.mul_sum]

theorem global_maximum_pairSum_real {z : Configuration} (hz : IsGlobalMaximum z)
    (h : Configuration) : 2 * (pairSum z h).re = 6 * (innerMoment z h).re := by
  have he := global_maximum_stationarity hz (motion z h) (by ext i; simp [motion])
    _ _ (hasDerivAt_normSum_motion z h) (hasDerivAt_discriminant_motion z h)
  have hp := global_maximum_positive hz
  nlinarith

theorem pairSum_mul (z h : Configuration) (c : ℂ) :
    pairSum z (fun i => c * h i) = c * pairSum z h := by
  unfold pairSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem innerMoment_mul (z h : Configuration) (c : ℂ) :
    innerMoment z (fun i => c * h i) = c * innerMoment z h := by
  unfold innerMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem global_maximum_pairSum {z : Configuration} (hz : IsGlobalMaximum z)
    (h : Configuration) : 2 * pairSum z h = 6 * innerMoment z h := by
  have hre := global_maximum_pairSum_real hz h
  have him := global_maximum_pairSum_real hz (fun i => Complex.I * h i)
  rw [pairSum_mul, innerMoment_mul] at him
  apply Complex.ext
  · simpa using hre
  · simpa using him

end N7.Analysis
