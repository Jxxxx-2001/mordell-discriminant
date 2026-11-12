import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Small trusted interface for elimination certificates. Each generated node has
an integer-cleared polynomial identity proved by `ring`. The lemmas below turn
that identity into a vanishing consequence in every commutative Q-algebra,
including algebras with zero divisors. No CAS result is taken as an assumption.
-/
namespace N6.Certificate

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem rat_scaled_zero (s : ℚ) (hs : s ≠ 0) (p : R)
    (h : algebraMap ℚ R s * p = 0) : p = 0 := by
  have hi : algebraMap ℚ R s⁻¹ * algebraMap ℚ R s = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hs, map_one]
  calc
    p = 1 * p := (one_mul p).symm
    _ = (algebraMap ℚ R s⁻¹ * algebraMap ℚ R s) * p := by rw [hi]
    _ = algebraMap ℚ R s⁻¹ * (algebraMap ℚ R s * p) := mul_assoc _ _ _
    _ = 0 := by rw [h, mul_zero]

theorem int_scaled_zero (s : ℤ) (hs : s ≠ 0) (p : R)
    (h : (s : R) * p = 0) : p = 0 := by
  apply rat_scaled_zero (s : ℚ) (Int.cast_ne_zero.mpr hs) p
  simpa only [map_intCast] using h

end N6.Certificate
