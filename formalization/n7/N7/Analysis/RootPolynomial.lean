import N7.PhysicalScalar
import N7.Analysis.Force
import N6.Analysis.RootPolynomial

set_option autoImplicit false

namespace N7.Analysis
open Polynomial

noncomputable def rootCofactor (w : Configuration) (i : Fin 7) : ℂ[X] :=
  ∏ j ∈ Finset.univ.erase i, (X - C (w j))

theorem rootProduct_factor (w : Configuration) (i : Fin 7) :
    rootProduct w = (X - C (w i)) * rootCofactor w i :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

theorem rootCofactor_eval_ne {w : Configuration} (hw : Function.Injective w)
    (i : Fin 7) : (rootCofactor w i).eval (w i) ≠ 0 := by
  simp only [rootCofactor, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (hw.ne (Finset.ne_of_mem_erase hj).symm)

theorem rootCofactor_logDerivative {w : Configuration} (hw : Function.Injective w)
    (i : Fin 7) :
    (rootCofactor w i).derivative.eval (w i) =
      (rootCofactor w i).eval (w i) * force w i := by
  have he := N6.eval_derivative_prod_relative (Finset.univ.erase i)
    (fun j => X - C (w j)) (w i) (by
      intro j hj
      simpa using sub_ne_zero.mpr (hw.ne (Finset.ne_of_mem_erase hj).symm))
  simpa only [rootCofactor, derivative_sub, derivative_X, derivative_C,
    sub_zero, eval_one, eval_sub, eval_X, eval_C, eval_prod,
    ← force_eq_sum_erase] using he

theorem rootProduct_derivative_eval (w : Configuration) (i : Fin 7) :
    (rootProduct w).derivative.eval (w i) = (rootCofactor w i).eval (w i) := by
  rw [rootProduct_factor w i]
  simp

theorem rootProduct_derivative_eval_ne {w : Configuration} (hw : Function.Injective w)
    (i : Fin 7) : (rootProduct w).derivative.eval (w i) ≠ 0 := by
  rw [rootProduct_derivative_eval]
  exact rootCofactor_eval_ne hw i

theorem rootProduct_second_derivative_eval {w : Configuration}
    (hw : Function.Injective w) (i : Fin 7) :
    (rootProduct w).derivative.derivative.eval (w i) =
      2 * (rootProduct w).derivative.eval (w i) * force w i := by
  rw [rootProduct_factor w i]
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X,
    derivative_C, sub_zero, derivative_one, eval_add, eval_mul, eval_zero,
    eval_one, eval_sub, eval_X, eval_C, sub_self, zero_mul, one_mul, zero_add,
    add_zero]
  rw [rootCofactor_logDerivative hw i]
  ring

end N7.Analysis
