import N6.Analysis.ResultantBridge
import N6.Analysis.SexticCoefficients
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace N6.Resultant6
open Polynomial

section Algebra
variable {R : Type*} [CommRing R]

def sexticVal (b c d e w : R) : R := w^6 + w^4 + b*w^3 + c*w^2 + d*w + e

def qVal (b c d U T w : R) : R :=
  (U+T*w) * (6*w^5 + 4*w^3 + 3*b*w^2 + 2*c*w + d) -
    (30*w^4 + 12*w^2 + 6*b*w + 2*c)

def seed (b c d e U T : R) : Fin 6 → R :=
  ![U*d-2*c-6*e*T, 2*c*U-6*b-5*d*T, 3*b*U-12-4*c*T,
    4*U-3*b*T, -30-2*T, 6*U]

def shift (b c d e : R) (v : Fin 6 → R) : Fin 6 → R :=
  ![-e*v 5, v 0-d*v 5, v 1-c*v 5, v 2-b*v 5, v 3-v 5, v 4]

def column (b c d e U T : R) : Nat → Fin 6 → R
  | 0 => seed b c d e U T
  | n+1 => shift b c d e (column b c d e U T n)

def presentation (b c d e U T : R) : Matrix (Fin 6) (Fin 6) R :=
  fun i j => column b c d e U T j.val i

def readCol (w : R) (v : Fin 6 → R) : R :=
  v 0 + w*v 1 + w^2*v 2 + w^3*v 3 + w^4*v 4 + w^5*v 5

theorem sum_readCol (w : R) (v : Fin 6 → R) :
    ∑ j : Fin 6, w^j.val * v j = readCol w v := by
  simp [Fin.sum_univ_succ, readCol] <;> ring

theorem readCol_shift (b c d e w : R) (hw : sexticVal b c d e w = 0) (v : Fin 6 → R) :
    readCol w (shift b c d e v) = w*readCol w v := by
  unfold sexticVal at hw
  simp [readCol, shift]
  linear_combination -(v 5)*hw

theorem readCol_seed (b c d e U T w : R) (hw : sexticVal b c d e w = 0) :
    readCol w (seed b c d e U T) = qVal b c d U T w := by
  unfold sexticVal at hw
  simp [readCol, seed, qVal]
  linear_combination (-6*T)*hw

theorem readCol_column (b c d e U T w : R) (hw : sexticVal b c d e w = 0) (n : Nat) :
    readCol w (column b c d e U T n) = qVal b c d U T w * w^n := by
  induction n with
  | zero => simpa [column] using readCol_seed b c d e U T w hw
  | succ n ih => rw [column, readCol_shift b c d e w hw, ih, pow_succ]; ring

theorem intertwine (b c d e U T : R) (w : Fin 6 → R) (hr : ∀ i, sexticVal b c d e (w i) = 0) :
    Matrix.vandermonde w * presentation b c d e U T =
    Matrix.diagonal (fun i => qVal b c d U T (w i)) * Matrix.vandermonde w := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [Matrix.vandermonde_apply, presentation]
  rw [sum_readCol]
  exact readCol_column b c d e U T (w i) (hr i) j.val

end Algebra

theorem det_presentation {R : Type*} [CommRing R] [IsDomain R] (b c d e U T : R)
    (w : Fin 6 → R) (hw : Function.Injective w) (hr : ∀ i, sexticVal b c d e (w i) = 0) :
    (presentation b c d e U T).det = ∏ i, qVal b c d U T (w i) := by
  have he := congrArg Matrix.det (intertwine b c d e U T w hr)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at he
  apply mul_left_cancel₀ (Matrix.det_vandermonde_ne_zero_iff.mpr hw)
  simpa only [mul_comm (∏ i, qVal b c d U T (w i)) (Matrix.vandermonde w).det] using he

theorem eval_q (b c d e U T w : ℂ) :
    (((C U + C T * X) * (N6.coefficientSextic 1 b c d e).derivative -
       (N6.coefficientSextic 1 b c d e).derivative.derivative).eval w) = qVal b c d U T w := by
  norm_num [N6.coefficientSextic, qVal, derivative_add, derivative_X_pow, derivative_C_mul_X_pow,
    derivative_C_mul_X, derivative_C_mul] <;> ring

theorem stationaryResultant_eq_det (w : N6.Configuration) (hw : Function.Injective w)
    (b c d e U T : ℂ) (hp : N6.rootPolynomial w = N6.coefficientSextic 1 b c d e) :
    N6.stationaryResultant w U T = (presentation b c d e U T).det := by
  have hr (i : Fin 6) : sexticVal b c d e (w i) = 0 := by
    have hh := N6.rootPolynomial_eval w i
    rw [hp] at hh
    simpa [N6.coefficientSextic, sexticVal] using hh
  rw [det_presentation b c d e U T w hw hr]
  unfold N6.stationaryResultant
  rw [N6.rootPolynomial_resultant]
  · apply Finset.prod_congr rfl
    intro i _
    rw [hp, eval_q]
  · have hd : (N6.rootPolynomial w).derivative.natDegree ≤ 5 := by
      simpa only [N6.rootPolynomial_natDegree] using (natDegree_derivative_le (p := N6.rootPolynomial w))
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      have hlin : (C U + C T * X).natDegree ≤ 1 := by
        apply (natDegree_add_le _ _).trans
        apply max_le
        · simp
        · exact (natDegree_C_mul_le _ _).trans (by simp)
      omega
    · have he := natDegree_derivative_le (p := (N6.rootPolynomial w).derivative)
      omega

#print axioms stationaryResultant_eq_det
end N6.Resultant6

