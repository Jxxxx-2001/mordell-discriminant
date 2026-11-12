-- Snapshot of the general n9-project tool; namespace isolated for n8.
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace MordellEight.Checks

def logSeries (t : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, t ^ (2*k+1) / (2*k+1)

def logError (t : ℚ) (n : ℕ) : ℚ := |t| ^ (2*n+1) / (1-t^2)

def logCheck (q lo hi : ℚ) (n : ℕ) : Bool :=
  let t := (q-1)/(q+1)
  decide (0 < q ∧ |t| < 1 ∧
    lo ≤ 2*(logSeries t n - logError t n) ∧
    2*(logSeries t n + logError t n) ≤ hi)

theorem logCheck_sound (q lo hi : ℚ) (n : ℕ) (h : logCheck q lo hi n = true) :
    (lo : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (hi : ℝ) := by
  let t : ℚ := (q-1)/(q+1)
  have hc : 0 < q ∧ |t| < 1 ∧
      lo ≤ 2*(logSeries t n - logError t n) ∧
      2*(logSeries t n + logError t n) ≤ hi := of_decide_eq_true h
  have ht : |(t : ℝ)| < 1 := by exact_mod_cast hc.2.1
  have hr : (1+t)/(1-t) = q := by
    dsimp [t]
    have hq : q+1 ≠ 0 := by linarith [hc.1]
    have hd : 1-(q-1)/(q+1) ≠ 0 := by
      intro hz
      have he : (q-1)/(q+1) = 1 := by linarith
      have he' := (div_eq_iff hq).mp he
      linarith
    field_simp [hq, hd]
    ring
  have hr' : (1+(t : ℝ))/(1-(t : ℝ)) = (q : ℝ) := by exact_mod_cast hr
  have hb := Real.sum_range_sub_log_div_le ht n
  rw [hr'] at hb
  have hs : (logSeries t n : ℝ) =
      ∑ k ∈ Finset.range n, (t : ℝ)^(2*k+1) / (2*k+1) := by
    simp [logSeries]
  have he : (logError t n : ℝ) = |(t : ℝ)|^(2*n+1)/(1-(t : ℝ)^2) := by
    simp [logError]
  rw [← hs, ← he] at hb
  have hlo : (lo : ℝ) ≤ 2*((logSeries t n : ℝ)-(logError t n : ℝ)) := by
    exact_mod_cast hc.2.2.1
  have hhi : 2*((logSeries t n : ℝ)+(logError t n : ℝ)) ≤ (hi : ℝ) := by
    exact_mod_cast hc.2.2.2
  have hh := abs_le.mp hb
  constructor <;> linarith

end MordellEight.Checks
