import N6.Weighted49.ArithmeticCore
import N6.Certificate
import N6.Saturation
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace N6.Weighted49
open scoped BigOperators

variable {R : Type*} [CommRing R]

def W {n : Nat} (basis : Fin n → R) (v : Fin n → ℤ) : R :=
  ∑ i, (v i : R) * basis i

theorem cast_sumInt {n : Nat} (v : Fin n → ℤ) :
    ((sumInt v : ℤ) : R) = ∑ i, (v i : R) := by
  induction n with
  | zero => simp [sumInt]
  | succ n ih =>
    rw [Fin.sum_univ_succ, sumInt, Int.cast_add, ih]

theorem W_zero {n : Nat} (basis : Fin n → R) :
    W basis (fun _ => (0 : ℤ)) = 0 := by simp [W]

theorem W_scale {n : Nat} (basis : Fin n → R) (a : ℤ) (v : Fin n → ℤ) :
    W basis (fun i => a*v i) = (a : R) * W basis v := by
  simp only [W, Int.cast_mul, Finset.mul_sum, mul_assoc]

theorem W_integer_linear_combination {n m : Nat} (basis : Fin n → R)
    (w : Fin m → ℤ) (v : Fin m → Fin n → ℤ) :
    W basis (fun i => sumInt (fun j => w j * v j i)) =
      ∑ j, (w j : R) * W basis (v j) := by
  simp only [W, cast_sumInt, Int.cast_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem W_matVec {n : Nat} (basis : Fin n → R) (M : Fin n → Fin n → ℤ)
    (G : ℤ) (x : R) (v : Fin n → ℤ)
    (columns : ∀ j, (G : R) * x * basis j = W basis (fun i => M i j)) :
    W basis (matVec M v) = (G : R) * x * W basis v := by
  have hv : matVec M v = fun i => sumInt (fun j => v j * M i j) := by
    funext i
    simp only [matVec, mul_comm]
  rw [hv, W_integer_linear_combination]
  simp_rw [← columns]
  simp only [W, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem cancelIntEq [Algebra ℚ R] (a : ℤ) (ha : a ≠ 0) {v w : R}
    (h : (a : R)*v = (a : R)*w) : v=w := by
  apply sub_eq_zero.mp
  apply N6.Certificate.int_scaled_zero a ha
  rw [mul_sub, h, sub_self]

/-- Both integer premises have the same orientation as the frozen action gate. -/
theorem action_gate [Algebra ℚ R] {n : Nat} (basis : Fin n → R) (M : Fin n → Fin n → ℤ)
    (G a b ds dt : ℤ) (x P : R) (src dst : Fin n → ℤ)
    (ha : a ≠ 0) (scaleEq : a*dt = b*G*ds)
    (vecEq : ∀ i, a*dst i = b*matVec M src i)
    (columns : ∀ j, (G : R)*x*basis j = W basis (fun i => M i j))
    (source : W basis src = (ds : R)*P) :
    W basis dst = (dt : R)*x*P := by
  apply cancelIntEq a ha
  calc
    (a : R) * W basis dst = W basis (fun i => a * dst i) := (W_scale basis a dst).symm
    _ = W basis (fun i => b * matVec M src i) := congrArg (W basis) (funext vecEq)
    _ = (b : R) * ((G : R)*x*((ds : R)*P)) := by rw [W_scale, W_matVec basis M G x src columns, source]
    _ = ((b*G*ds : ℤ) : R) * (x*P) := by simp only [Int.cast_mul]; ring
    _ = ((a*dt : ℤ) : R) * (x*P) := by rw [scaleEq]
    _ = (a : R)*((dt : R)*x*P) := by simp only [Int.cast_mul]; ring

/-- The cleared 76-term D initialization, with separate exact integer weights. -/
theorem sum_gate [Algebra ℚ R] {n m : Nat} (basis : Fin n → R)
    (w ds c : Fin m → ℤ) (src : Fin m → Fin n → ℤ) (mon : Fin m → R)
    (dst : Fin n → ℤ) (a dt : ℤ) (ha : a ≠ 0)
    (vecEq : ∀ i, a*dst i = sumInt (fun j => w j * src j i))
    (weightEq : ∀ j, w j * ds j = a * dt * c j)
    (source : ∀ j, W basis (src j) = (ds j : R)*mon j) :
    W basis dst = (dt : R) * ∑ j, (c j : R)*mon j := by
  apply cancelIntEq a ha
  calc
    (a : R)*W basis dst = W basis (fun i => a*dst i) := (W_scale basis a dst).symm
    _ = W basis (fun i => sumInt (fun j => w j * src j i)) := congrArg (W basis) (funext vecEq)
    _ = ∑ j, (w j : R) * W basis (src j) := W_integer_linear_combination basis w src
    _ = ∑ j, ((a : R)*(dt : R)) * ((c j : R)*mon j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [source j]
      calc
        (w j : R)*((ds j : R)*mon j) = ((w j * ds j : ℤ) : R)*mon j := by
          rw [Int.cast_mul, mul_assoc]
        _ = ((a : R)*(dt : R))*((c j : R)*mon j) := by
          rw [weightEq j]; simp only [Int.cast_mul]; ring
    _ = (a : R)*((dt : R) * ∑ j, (c j : R)*mon j) := by rw [← Finset.mul_sum, mul_assoc]

/-- The step accepts precisely the source invariant required by action_gate. -/
theorem weighted_sequence {n : Nat} (B D : R) (d : Fin (n+1) → ℤ)
    (L : Fin (n+1) → R) (h0 : L 0 = (d 0 : R)*D)
    (step : ∀ (i : Fin n) (P : R), L i.castSucc = (d i.castSucc : R)*P →
      L i.succ = (d i.succ : R)*B*P) :
    ∀ i, L i = (d i : R)*(D*B^i.val) := by
  apply Fin.induction
  · simpa using h0
  · intro i ih
    have h := step i (D*B^i.val) ih
    rw [h]
    simp only [Fin.val_succ, pow_succ]
    ring

/-- Use the coordinate vector, when present, as one more summand in the same row.
    The removed gcd g is multiplied back before cancelling L and then D. -/
theorem cancel_weighted_row [Algebra ℚ R] {n m : Nat} (basis : Fin n → R)
    (w d c : Fin m → ℤ) (src : Fin m → Fin n → ℤ) (mon : Fin m → R)
    (g L : ℤ) (t B D : R) (hL : L ≠ 0) (hS : t*B*D-1=0)
    (vecZero : ∀ i, sumInt (fun j => w j * src j i) = 0)
    (weightEq : ∀ j, g*w j*d j = L*c j)
    (source : ∀ j, W basis (src j) = (d j : R)*(D*mon j)) :
    (∑ j, (c j : R)*mon j) = 0 := by
  have row : (∑ j, (w j : R)*W basis (src j)) = 0 := by
    rw [← W_integer_linear_combination basis w src]
    exact (congrArg (W basis) (funext vecZero)).trans (W_zero basis)
  apply N6.Saturation.cancel_D t B D _ hS
  apply N6.Certificate.int_scaled_zero L hL
  calc
    (L : R)*(D*∑ j, (c j : R)*mon j) = ∑ j, ((L : R)*D)*((c j : R)*mon j) := by
      rw [← mul_assoc, Finset.mul_sum]
    _ = ∑ j, (g : R)*((w j : R)*W basis (src j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [source j]
      calc
        ((L : R)*D)*((c j : R)*mon j) = ((L*c j : ℤ) : R)*(D*mon j) := by
          simp only [Int.cast_mul]; ring
        _ = ((g*w j*d j : ℤ) : R)*(D*mon j) := by rw [weightEq j]
        _ = (g : R)*((w j : R)*((d j : R)*(D*mon j))) := by simp only [Int.cast_mul]; ring
    _ = 0 := by rw [← Finset.mul_sum, row, mul_zero]

#print axioms action_gate
#print axioms sum_gate
#print axioms weighted_sequence
#print axioms cancel_weighted_row
end N6.Weighted49
