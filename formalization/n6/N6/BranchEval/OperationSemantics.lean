import N6.Certificate
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace N6.BranchEval

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- A checked polynomial certificate, evaluated at any root of its factor. -/
theorem reduction_at_root (s : ℤ) (hs : s ≠ 0) {residual f q : R}
    (hf : f = 0) (cert : (s : R)*residual = f*q) : residual = 0 := by
  apply N6.Certificate.int_scaled_zero s hs
  rw [cert, hf, zero_mul]

/-- Numerator values use the invariant n = d * representedValue. -/
theorem add_gate (s da db dout : ℤ) (hs : s ≠ 0) (ha : da ≠ 0) (hb : db ≠ 0)
    {f q na nb nout a b : R} (hf : f = 0)
    (sourceA : na = (da : R)*a) (sourceB : nb = (db : R)*b)
    (cert : (s : R)*((dout : R)*((db : R)*na+(da : R)*nb) -
      (da : R)*(db : R)*nout) = f*q) :
    nout = (dout : R)*(a+b) := by
  have h := reduction_at_root s hs hf cert
  rw [sourceA, sourceB] at h
  apply sub_eq_zero.mp
  apply N6.Certificate.int_scaled_zero (da*db) (mul_ne_zero ha hb)
  rw [Int.cast_mul]
  linear_combination -h

theorem mul_gate (s da db dout : ℤ) (hs : s ≠ 0) (ha : da ≠ 0) (hb : db ≠ 0)
    {f q na nb nout a b : R} (hf : f = 0)
    (sourceA : na = (da : R)*a) (sourceB : nb = (db : R)*b)
    (cert : (s : R)*((dout : R)*na*nb - (da : R)*(db : R)*nout) = f*q) :
    nout = (dout : R)*(a*b) := by
  have h := reduction_at_root s hs hf cert
  rw [sourceA, sourceB] at h
  apply sub_eq_zero.mp
  apply N6.Certificate.int_scaled_zero (da*db) (mul_ne_zero ha hb)
  rw [Int.cast_mul]
  linear_combination -h

/-- Identical normal forms on the two sides of an archived endpoint check. -/
theorem same_normal_form (d : ℤ) (hd : d ≠ 0) {numerator a b : R}
    (left : numerator = (d : R)*a) (right : numerator = (d : R)*b) : a = b := by
  apply sub_eq_zero.mp
  apply N6.Certificate.int_scaled_zero d hd
  rw [mul_sub, ← left, ← right, sub_self]

/-- Project the actual lex row A*y+H=0 onto the local coordinate n/d. -/
theorem project_coordinate (A d : ℤ) (hA : A ≠ 0) {y H n f q : R}
    (row : (A : R)*y + H = 0) (hf : f = 0)
    (cert : (d : R)*H + (A : R)*n = f*q) : (d : R)*y = n := by
  have h : (d : R)*H + (A : R)*n = 0 := by rw [cert, hf, zero_mul]
  apply sub_eq_zero.mp
  apply N6.Certificate.int_scaled_zero A hA
  linear_combination (d : R)*row - h

#print axioms add_gate
#print axioms mul_gate
#print axioms same_normal_form
#print axioms project_coordinate
end N6.BranchEval
