import N6.ResultantMinors.CoefficientCore
import N6.ResultantMinors.Bindings
import Mathlib.Algebra.Polynomial.Coeff

set_option autoImplicit false

namespace N6.ResultantMinors
open N6.SparseCheck Polynomial

/-- Hold b,c,d,e fixed and retain Y as the polynomial indeterminate. -/
noncomputable def liftY (b c d e : ℂ) : Poly → ℂ[X]
  | [] => 0
  | a :: p =>
    C ((a.2 : ℂ) * (e^a.1.e * d^a.1.k * c^a.1.c * b^a.1.b)) * X^a.1.t +
      liftY b c d e p

theorem eval_liftY (b c d e U : ℂ) (p : Poly) :
    (liftY b c d e p).eval U = value (point b c d e U) p := by
  induction p with
  | nil => simp [liftY, value]
  | cons a p ih =>
    simp [liftY, value, monVal, point, ih] <;> ring

theorem coeff_liftY (b c d e : ℂ) (p : Poly) (n : Nat) :
    (liftY b c d e p).coeff n = value (point b c d e 0) (extractY n p) := by
  induction p with
  | nil => simp [liftY, extractY, value]
  | cons a p ih =>
    simp only [liftY, coeff_add, coeff_C_mul, coeff_X_pow, ih]
    by_cases h : a.1.t = n
    · simp [extractY, h, value, monVal, point] <;> ring
    · simp [extractY, h, Ne.symm h]

#print axioms eval_liftY
#print axioms coeff_liftY
end N6.ResultantMinors
