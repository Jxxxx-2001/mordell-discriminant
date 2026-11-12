import N6.CertificateCore
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.Ring

namespace N6.SparseCheck

section Soundness

variable {R : Type*} [CommRing R] (x : Fin 5 → R)

def monVal (m : Mon) : R :=
  x 0 ^ m.t * x 1 ^ m.e * x 2 ^ m.k * x 3 ^ m.c * x 4 ^ m.b

def value : Poly → R
  | [] => 0
  | a :: p => (a.2 : R) * monVal x a.1 + value p

theorem monVal_plus (u v : Mon) :
    monVal x (u.plus v) = monVal x u * monVal x v := by
  simp only [monVal, Mon.plus, pow_add]
  ring

theorem value_append (p q : Poly) : value x (p ++ q) = value x p + value x q := by
  induction p with
  | nil => simp [value]
  | cons a rest ih => simp [value, ih, add_assoc]

theorem value_mergeAux (n : Nat) (p q : Poly) :
    value x (mergeAux n p q) = value x p + value x q := by
  induction n generalizing p q with
  | zero => exact value_append x p q
  | succ n ih =>
    cases p with
    | nil => simp [mergeAux, value]
    | cons a p =>
      cases q with
      | nil => simp [mergeAux, value]
      | cons b q =>
        obtain ⟨u, i⟩ := a
        obtain ⟨v, j⟩ := b
        by_cases h : u = v
        · subst v
          simp only [mergeAux, if_pos, value, ih, Int.cast_add]
          ring
        · by_cases hlt : u.key < v.key
          · simp [mergeAux, h, hlt, value, ih, add_assoc]
          · simp [mergeAux, h, hlt, value, ih, add_assoc, add_left_comm, add_comm]

theorem value_merge (p q : Poly) : value x (merge p q) = value x p + value x q :=
  value_mergeAux x _ p q

theorem value_mapMul (a : Term) (p : Poly) :
    value x (p.map (mulTerm a)) = (a.2 : R) * monVal x a.1 * value x p := by
  induction p with
  | nil => simp [value]
  | cons b p ih =>
    simp only [List.map_cons, value, mulTerm, Int.cast_mul, monVal_plus, ih]
    ring

theorem value_mul (p q : Poly) : value x (mul p q) = value x p * value x q := by
  induction p with
  | nil => simp [mul, value]
  | cons a p ih =>
    simp only [mul, value, value_merge, value_mapMul, ih]
    ring

theorem value_zero {p : Poly} (h : zero p = true) : value x p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [zero, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [value, h.1, ih h.2]

end Soundness

-- Concrete smoke test for the closed kernel reduction and its semantic bridge.
theorem smokeZero : zero (merge (mul smokeP smokeP) (mul smokeN smokeP)) = true := by decide
theorem smokeSemantic {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x smokeP * value x smokeP + value x smokeN * value x smokeP = 0 := by
  simpa only [value_merge, value_mul] using value_zero x smokeZero

end N6.SparseCheck
