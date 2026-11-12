import N6.Analysis.ResultantBridge
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

namespace N6.Resultant6

/-- One row-zero expansion of the value and first derivative of a determinant.
    The cofactor uses the unsigned minor; this lemma inserts (-1)^j once. -/
theorem det_row_zero_jet {n : Nat}
    (M : ℂ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (e e' d d' : Fin (n+1) → ℂ)
    (he : ∀ j, M 0 0 j = e j)
    (he' : ∀ j, HasDerivAt (fun T : ℂ => M T 0 j) (e' j) 0)
    (hd : ∀ j : Fin (n+1), ((M 0).submatrix Fin.succ j.succAbove).det = d j)
    (hd' : ∀ j : Fin (n+1), HasDerivAt (fun T : ℂ =>
      ((M T).submatrix Fin.succ j.succAbove).det) (d' j) 0) :
    ((M 0).det = ∑ j : Fin (n+1), (-1 : ℂ)^j.val * e j * d j) ∧
    HasDerivAt (fun T : ℂ => (M T).det)
      (∑ j : Fin (n+1), (-1 : ℂ)^j.val * (e' j * d j + e j * d' j)) 0 := by
  constructor
  · rw [Matrix.det_succ_row_zero]
    simp only [he, hd]
  · have expand : (fun T : ℂ => (M T).det) =
        (fun T : ℂ => ∑ j : Fin (n+1), (-1 : ℂ)^j.val * M T 0 j *
          ((M T).submatrix Fin.succ j.succAbove).det) := by
      funext T
      exact Matrix.det_succ_row_zero (M T)
    rw [expand]
    apply HasDerivAt.fun_sum
    intro j _
    simpa only [Pi.mul_apply, he j, hd j, mul_assoc] using
      (((he' j).mul (hd' j)).const_mul ((-1 : ℂ)^j.val))

#print axioms det_row_zero_jet
end N6.Resultant6

