import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Chalk

theorem twice_pairs (p : ℕ) : (p+2).choose 2 * 2 = (p+2)*(p+1) := by
  simpa using (Nat.add_one_mul_choose_eq (p+1) 1).symm

private theorem coarse (p : ℕ) (hp : 23 ≤ p) :
    (p+1)^4*(p+3)^2 < 16*2^(p+1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hp
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      _ < 2*((23+k+1)^4*(23+k+3)^2) := by ring_nf; omega
      _ < 2*(16*2^(23+k+1)) := by omega
      _ = _ := by rw [show 23+k.succ+1 = (23+k+1)+1 by omega, pow_succ]; ring

private theorem large (p : ℕ) (hp : 23 ≤ p) :
    (p+1)^(p+1)*(p+2)^((p+2).choose 2) <
      4*p^p*(p+3)^((p+2).choose 2-1) := by
  let N := (p+2).choose 2
  have hN : N*2=(p+2)*(p+1) := twice_pairs p
  have hpos : 0<N := by by_contra! h; simp [show N=0 by omega] at hN
  let x : ℝ := p
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hx1 : 0 < x+1 := by positivity
  have hx2 : 0 < x+2 := by positivity
  have hx3 : 0 < x+3 := by positivity
  have ha := one_add_mul_le_pow (a := -(1/(x+1))) (by
    have : 1/(x+1) ≤ 1 := (div_le_one hx1).mpr (by linarith)
    linarith) p
  change 1+x * -(1/(x+1)) ≤ _ at ha
  rw [show 1+x * -(1/(x+1)) = 1/(x+1) by field_simp; ring,
      show 1 + -(1/(x+1)) = x/(x+1) by field_simp; ring, div_pow] at ha
  have hA := (div_le_div_iff₀ hx1 (pow_pos hx1 p)).mp ha
  have hb := one_add_mul_le_pow (a := 1/(x+2)) (by linarith [show 0 ≤ 1/(x+2) by positivity]) (p+2)
  rw [show ((p+2:ℕ):ℝ) = x+2 by simp [x],
      show 1+(x+2)*(1/(x+2))=2 by field_simp; ring,
      show 1+1/(x+2)=(x+3)/(x+2) by field_simp; ring] at hb
  have hB := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hb (p+1)
  rw [← pow_mul, ← hN, pow_mul] at hB
  have hC : (x+1)^4*(x+3)^2 < 16*(2:ℝ)^(p+1) := by
    dsimp [x]; exact_mod_cast coarse p hp
  let r := ((x+3)/(x+2))^N
  have hD : (x+1)^2*(x+3) < 4*r := by
    have hh : ((x+1)^2*(x+3))^2 < (4*r)^2 := by
      nlinarith only [hC, hB, show r=((x+3)/(x+2))^N from rfl]
    exact lt_of_pow_lt_pow_left₀ 2 (by dsimp [r]; positivity) hh
  change _ < 4*((x+3)/(x+2))^N at hD
  rw [div_pow, ←mul_div_assoc] at hD
  have hE := (lt_div_iff₀ (pow_pos hx2 N)).mp hD
  have hF : (x+1)^p*(x+1)*(x+2)^N < 4*x^p*(x+3)^(N-1) := by
    apply lt_of_mul_lt_mul_right (a := x+3) _ hx3.le
    calc
      _ ≤ (x^p*(x+1))*(x+1)*(x+2)^N*(x+3) := by
        gcongr; simpa [mul_comm] using hA
      _ < x^p*(4*(x+3)^N) := by
        convert mul_lt_mul_of_pos_left hE (show 0 < x^p by
          dsimp [x]; positivity) using 1; ring
      _ = _ := by rw [show (x+3)^N=(x+3)^(N-1)*(x+3) by
                            rw [←pow_succ]; congr 1; omega]; ring
  rw [← pow_succ] at hF
  dsimp [x,N] at hF
  exact_mod_cast hF

/-- The natural-number comparison used by the normalized configuration. -/
theorem integer_bound (n : ℕ) (hn : 10 ≤ n) :
    (n-1)^(n-1)*n^(n*(n-1)/2) < 4*(n-2)^(n-2)*(n+1)^(n*(n-1)/2-1) := by
  by_cases h : n ≤ 24
  · interval_cases n <;> decide +kernel
  · obtain ⟨p,rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
    simpa [Nat.choose_two_right, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      large p (by omega)

end Chalk
