import N6.Analysis.DualStationarity
import Mathlib.RingTheory.Polynomial.Resultant.Basic

set_option autoImplicit false

namespace N6
open Polynomial

/-- The actual resultant with degree bounds (6, 6), hence a 12-by-12 Sylvester matrix, before setting the motion parameter to zero. -/
noncomputable def stationaryResultant (x : Configuration) (U T : ℂ) : ℂ :=
  (rootPolynomial x).resultant
    ((C U + C T * X) * (rootPolynomial x).derivative -
      (rootPolynomial x).derivative.derivative) 6 6

theorem rootPolynomial_resultant (x : Configuration) (q : ℂ[X]) (n : ℕ)
    (hq : q.natDegree ≤ n) :
    (rootPolynomial x).resultant q 6 n = ∏ i, q.eval (x i) := by
  have hd := rootPolynomial_natDegree x
  unfold rootPolynomial at hd ⊢
  have he := resultant_prod_left (Finset.univ : Finset (Fin 6))
    (fun i => X - C (x i)) q n (by simp) hq
  rw [hd] at he
  simpa only [natDegree_X_sub_C, resultant_X_sub_C_left q n _ hq] using he

/-- This factorization uses only the force equation at the six original roots. -/
theorem stationaryResultant_product {x y : Configuration}
    (h : DualStationaryPair x y) (U T : ℂ) :
    stationaryResultant x U T =
      complexDiscriminant x * ∏ i, (U + T * x i - y i) := by
  unfold stationaryResultant
  rw [rootPolynomial_resultant]
  · simp only [eval_sub, eval_mul, eval_add, eval_C, eval_X,
      dualStationaryPair_root_equation h]
    unfold complexDiscriminant
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    ring
  · have hd : (rootPolynomial x).derivative.natDegree ≤ 5 := by
      have he := natDegree_derivative_le (p := rootPolynomial x)
      simpa only [rootPolynomial_natDegree] using he
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      have hlin : (C U + C T * X).natDegree ≤ 1 := by
        apply (natDegree_add_le _ _).trans
        apply max_le
        · simp
        · exact (natDegree_C_mul_le _ _).trans (by simp)
      omega
    · have he := natDegree_derivative_le (p := (rootPolynomial x).derivative)
      omega

theorem stationaryResultant_at_zero {x y : Configuration}
    (h : DualStationaryPair x y) (U : ℂ) :
    stationaryResultant x U 0 = (stationaryR0 x y).eval U := by
  rw [stationaryResultant_product h]
  simp only [stationaryR0, rootPolynomial, eval_mul, eval_C, eval_prod,
    eval_sub, eval_X, zero_mul, add_zero]

/-- Differentiating in T gives the weighted cofactor polynomial, including at its roots. -/
theorem stationaryResultant_hasDerivAt {x y : Configuration}
    (h : DualStationaryPair x y) (U : ℂ) :
    HasDerivAt (fun T : ℂ => stationaryResultant x U T)
      ((stationaryRT x y).eval U) 0 := by
  have hd : HasDerivAt (fun T : ℂ => ∏ i, (U + T * x i - y i))
      (∑ i, (∏ j ∈ Finset.univ.erase i, (U - y j)) * x i) 0 := by
    have hf : ∀ i ∈ (Finset.univ : Finset (Fin 6)),
        HasDerivAt (fun T : ℂ => U + T * x i - y i) (x i) 0 := by
      intro i _
      simpa using (((hasDerivAt_id (0 : ℂ)).mul_const (x i)).const_add U).sub_const (y i)
    simpa only [zero_mul, add_zero, smul_eq_mul] using HasDerivAt.fun_finsetProd hf
  have hc : complexDiscriminant x *
      (∑ i, (∏ j ∈ Finset.univ.erase i, (U - y j)) * x i) =
      (stationaryRT x y).eval U := by
    simp only [stationaryRT, rootCofactor, eval_mul, eval_C, eval_finsetSum,
      eval_prod, eval_sub, eval_X]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he : (fun T : ℂ => stationaryResultant x U T) =
      (fun T : ℂ => complexDiscriminant x * ∏ i, (U + T * x i - y i)) := by
    funext T
    exact stationaryResultant_product h U T
  rw [he]
  rw [← hc]
  exact hd.const_mul (complexDiscriminant x)

theorem stationaryResultant_deriv {x y : Configuration}
    (h : DualStationaryPair x y) (U : ℂ) :
    deriv (fun T : ℂ => stationaryResultant x U T) 0 = (stationaryRT x y).eval U :=
  (stationaryResultant_hasDerivAt h U).deriv

/-- The resultant identity follows from the two force equations, with no coefficient assumptions. -/
theorem stationaryResultant_deriv_eq_second {x y : Configuration}
    (h : DualStationaryPair x y) (U : ℂ) :
    deriv (fun T : ℂ => stationaryResultant x U T) 0 =
      (stationaryR0 x y).derivative.derivative.eval U := by
  rw [stationaryResultant_deriv h,
    stationaryRT_eq_second x y h.right_injective h.right_force]

theorem scaled_maximum_resultant_deriv_eq_second {z : Configuration}
    (hz : IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0) (U : ℂ) :
    deriv (fun T : ℂ => stationaryResultant (scaleConfiguration α z) U T) 0 =
      (stationaryR0 (scaleConfiguration α z)
        (dualConfiguration (scaleConfiguration α z))).derivative.derivative.eval U := by
  exact stationaryResultant_deriv_eq_second (scaled_dualStationaryPair hz hα) U

end N6
