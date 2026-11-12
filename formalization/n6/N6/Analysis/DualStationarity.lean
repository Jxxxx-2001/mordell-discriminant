import N6.Analysis.Normalization
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false

namespace N6
open Polynomial

/-- The force equations alone, with the original index correspondence retained. -/
structure DualStationaryPair (x y : Configuration) : Prop where
  left_injective : Function.Injective x
  right_injective : Function.Injective y
  left_force : ∀ i, (2 : ℂ) * force x i = y i
  right_force : ∀ i, (2 : ℂ) * force y i = x i

theorem scaled_dualStationaryPair {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) :
    DualStationaryPair (scaleConfiguration α z) (dualConfiguration (scaleConfiguration α z)) := by
  refine ⟨scaled_injective hz hα, scaled_dual_injective hz hα, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    rw [scaled_dual_force hz hα i]
    ring

theorem dualStationaryPair_root_equation {x y : Configuration}
    (h : DualStationaryPair x y) (i : Fin 6) :
    (rootPolynomial x).derivative.derivative.eval (x i) =
      y i * (rootPolynomial x).derivative.eval (x i) := by
  rw [rootPolynomial_second_derivative_eval h.left_injective]
  calc
    2 * (rootPolynomial x).derivative.eval (x i) * force x i =
        (rootPolynomial x).derivative.eval (x i) * (2 * force x i) := by ring
    _ = (rootPolynomial x).derivative.eval (x i) * y i := by rw [h.left_force i]
    _ = y i * (rootPolynomial x).derivative.eval (x i) := by ring

noncomputable def complexDiscriminant (x : Configuration) : ℂ :=
  ∏ i, (rootPolynomial x).derivative.eval (x i)

theorem complexDiscriminant_ne {x : Configuration} (hx : Function.Injective x) :
    complexDiscriminant x ≠ 0 := by
  unfold complexDiscriminant
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact normalization_derivative_eval_ne hx i

noncomputable def stationaryR0 (x y : Configuration) : ℂ[X] :=
  C (complexDiscriminant x) * rootPolynomial y

noncomputable def stationaryRT (x y : Configuration) : ℂ[X] :=
  C (complexDiscriminant x) * ∑ i, C (x i) * rootCofactor y i

theorem stationaryR0_coeff_six (x y : Configuration) :
    (stationaryR0 x y).coeff 6 = complexDiscriminant x := by
  have hc : (rootPolynomial y).coeff 6 = 1 := by
    rw [← rootPolynomial_natDegree y]
    exact (rootPolynomial_monic y).coeff_natDegree
  simp only [stationaryR0, coeff_C_mul, hc, mul_one]

theorem stationaryR0_coeff_six_ne {x y : Configuration} (hx : Function.Injective x) :
    (stationaryR0 x y).coeff 6 ≠ 0 := by
  rw [stationaryR0_coeff_six]
  exact complexDiscriminant_ne hx

theorem rootCofactor_natDegree (y : Configuration) (i : Fin 6) :
    (rootCofactor y i).natDegree = 5 := by
  unfold rootCofactor
  rw [natDegree_prod_of_monic (Finset.univ.erase i : Finset (Fin 6))
    (fun j => X - C (y j)) (fun j _ => monic_X_sub_C (y j))]
  simp

theorem rootCofactor_eval_off (y : Configuration) {i j : Fin 6} (hij : i ≠ j) :
    (rootCofactor y j).eval (y i) = 0 := by
  simp only [rootCofactor, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_eq_zero_iff.mpr
  exact ⟨i, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩, by simp⟩

theorem stationaryRT_eval_at_root (x y : Configuration) (i : Fin 6) :
    (stationaryRT x y).eval (y i) =
      complexDiscriminant x * x i * (rootPolynomial y).derivative.eval (y i) := by
  simp only [stationaryRT, eval_mul, eval_C, eval_finsetSum]
  rw [Finset.sum_eq_single i]
  · rw [rootPolynomial_derivative_eval]
    ring
  · intro j _ hji
    rw [rootCofactor_eval_off y hji.symm, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem stationaryR0_second_eval_at_root (x y : Configuration)
    (hy : Function.Injective y) (hforce : ∀ i, (2 : ℂ) * force y i = x i) (i : Fin 6) :
    (stationaryR0 x y).derivative.derivative.eval (y i) =
      complexDiscriminant x * x i * (rootPolynomial y).derivative.eval (y i) := by
  simp only [stationaryR0, derivative_mul, derivative_C, zero_mul, zero_add,
    eval_mul, eval_C]
  rw [rootPolynomial_second_derivative_eval hy]
  calc
    complexDiscriminant x * (2 * (rootPolynomial y).derivative.eval (y i) * force y i) =
        complexDiscriminant x * ((rootPolynomial y).derivative.eval (y i) *
          (2 * force y i)) := by ring
    _ = complexDiscriminant x * ((rootPolynomial y).derivative.eval (y i) * x i) := by
      rw [hforce i]
    _ = complexDiscriminant x * x i * (rootPolynomial y).derivative.eval (y i) := by ring

theorem stationaryRT_natDegree_le (x y : Configuration) :
    (stationaryRT x y).natDegree ≤ 5 := by
  unfold stationaryRT
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans (le_of_eq (rootCofactor_natDegree y i))

theorem stationaryR0_second_natDegree_le (x y : Configuration) :
    (stationaryR0 x y).derivative.derivative.natDegree ≤ 4 := by
  have hp : (stationaryR0 x y).natDegree ≤ 6 := by
    unfold stationaryR0
    exact (natDegree_C_mul_le _ _).trans (le_of_eq (rootPolynomial_natDegree y))
  have h1 := natDegree_derivative_le (p := stationaryR0 x y)
  have h2 := natDegree_derivative_le (p := (stationaryR0 x y).derivative)
  omega

/-- Six distinct dual roots determine the two polynomials of degree at most five. -/
theorem stationaryRT_eq_second (x y : Configuration) (hy : Function.Injective y)
    (hforce : ∀ i, (2 : ℂ) * force y i = x i) :
    stationaryRT x y = (stationaryR0 x y).derivative.derivative := by
  apply eq_of_natDegree_lt_card_of_eval_eq _ _ hy
  · intro i
    rw [stationaryRT_eval_at_root, stationaryR0_second_eval_at_root x y hy hforce]
  · have ht := stationaryRT_natDegree_le x y
    have h0 := stationaryR0_second_natDegree_le x y
    simp only [Fintype.card_fin]
    omega

def RawStationaryEquations (x y : Configuration) : Prop :=
  (stationaryRT x y).coeff 3 = 0 ∧
  (stationaryRT x y).coeff 2 - 12 * (stationaryR0 x y).coeff 4 = 0 ∧
  (stationaryRT x y).coeff 1 - 6 * (stationaryR0 x y).coeff 3 = 0 ∧
  (stationaryRT x y).coeff 0 - 2 * (stationaryR0 x y).coeff 2 = 0

theorem rawStationaryEquations_of_dual_force (x y : Configuration)
    (hy : Function.Injective y) (hcenter : ∑ i, y i = 0)
    (hforce : ∀ i, (2 : ℂ) * force y i = x i) : RawStationaryEquations x y := by
  have he := stationaryRT_eq_second x y hy hforce
  have h5 : (stationaryR0 x y).coeff 5 = 0 := by
    simp only [stationaryR0, coeff_C_mul, rootPolynomial_coeff_five, hcenter,
      neg_zero, mul_zero]
  unfold RawStationaryEquations
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals rw [he]
  all_goals norm_num [coeff_derivative, h5] <;> ring

theorem scaled_maximum_RT_eq_second {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) :
    stationaryRT (scaleConfiguration α z) (dualConfiguration (scaleConfiguration α z)) =
      (stationaryR0 (scaleConfiguration α z)
        (dualConfiguration (scaleConfiguration α z))).derivative.derivative := by
  exact stationaryRT_eq_second _ _ (scaled_dual_injective hz hα)
    (scaled_dualStationaryPair hz hα).right_force

theorem scaled_maximum_rawStationaryEquations {z : Configuration}
    (hz : IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0) :
    RawStationaryEquations (scaleConfiguration α z)
      (dualConfiguration (scaleConfiguration α z)) := by
  exact rawStationaryEquations_of_dual_force _ _ (scaled_dual_injective hz hα)
    (scaled_dual_centered hz hα) (scaled_dualStationaryPair hz hα).right_force

end N6
