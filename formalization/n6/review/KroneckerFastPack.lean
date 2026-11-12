import N6.CertificateCore
import review.KroneckerCheck
import Mathlib.Data.Int.Bitwise

namespace N6.KroneckerFastPack
open N6.SparseCheck N6.KroneckerCheck

theorem shifted_eq (bits offset : Nat) (v : Int) : shifted bits offset v = v * place bits offset := by
  unfold shifted
  rw [← Int.shiftLeft_natCast_right v (bits * offset)]
  rw [Int.shiftLeft_eq_mul_pow]
  simp [place, Nat.shiftLeft_eq]

theorem weighted_split (bits h : Nat) (p : List Digit) :
    weighted bits (lower h p) + shifted bits h (weighted bits (upperDigits h p)) =
      weighted bits p := by
  rw [shifted_eq]
  induction p with
  | nil => simp [lower, upperDigits, weighted]
  | cons a p ih =>
    by_cases ha : a.1 < h
    · have hn : ¬ h ≤ a.1 := Nat.not_le.mpr ha
      simpa [lower, upperDigits, weighted, ha, hn, add_assoc] using
        congrArg (fun v : Int => a.2 * place bits a.1 + v) ih
    · have hn : h ≤ a.1 := Nat.le_of_not_gt ha
      have pw : place bits (a.1 - h) * place bits h = place bits a.1 := by
        simp only [place_eq, ← pow_add, Nat.sub_add_cancel hn]
      have coeff : (a.2 * place bits (a.1 - h)) * place bits h = a.2 * place bits a.1 := by
        rw [mul_assoc, pw]
      calc
        weighted bits (lower h (a :: p)) +
            weighted bits (upperDigits h (a :: p)) * place bits h =
            weighted bits (lower h p) +
              (a.2 * place bits (a.1-h) + weighted bits (upperDigits h p)) * place bits h := by
                simp [lower, upperDigits, weighted, ha, hn]
        _ = a.2 * place bits a.1 +
              (weighted bits (lower h p) + weighted bits (upperDigits h p) * place bits h) := by
                rw [add_mul, coeff]
                ac_rfl
        _ = weighted bits (a::p) := by rw [ih]; rfl

/-- Empty and singleton subtrees terminate immediately. The fallback at depth zero
    preserves all remaining key bits, so soundness never depends on a depth bound. -/
theorem aux_eq (bits n : Nat) (p : List Digit) : aux bits n p = weighted bits p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      cases p with
      | nil => simp [aux, weighted, shifted_eq]
      | cons b p => simpa only [aux, ih] using weighted_split bits (2^n) (a::b::p)

theorem fastPack_eq (r : Rad) (bits depth : Nat) (p : Poly) :
    fastPack r bits depth p = pack r bits p := by
  unfold fastPack
  rw [aux_eq]
  induction p with
  | nil => rfl
  | cons a p ih =>
    change a.2 * place bits (code r a.1) + weighted bits (digits r p) =
      a.2 * place bits (code r a.1) + pack r bits p
    rw [ih]

theorem pairs_fastPack_eq (r : Rad) (bits depth : Nat) (ps : Products) :
    pairs (fastPack r bits depth) ps = pairs (pack r bits) ps := by
  rw [show fastPack r bits depth = pack r bits from funext (fastPack_eq r bits depth)]

#print axioms pairs_fastPack_eq
end N6.KroneckerFastPack
