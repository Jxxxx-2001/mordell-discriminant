import N6.Even.RawBindings
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace N6.Even

/-- A coarse initial interval is enough for the exact value cover. -/
theorem p6_real_root_bounds (c : ℝ) (hp : p6 c = 0) : -10 ≤ c ∧ c ≤ 10 := by
  simp only [p6, mul_eq_zero] at hp
  rcases hp with (h | h) | h
  · constructor <;> linarith
  · constructor
    · by_contra hc
      have hc : c < -10 := lt_of_not_ge hc
      have hm := mul_nonneg_of_nonpos_of_nonpos
        (show c ≤ 0 by linarith) (show c+10 ≤ 0 by linarith)
      nlinarith
    · nlinarith [sq_nonneg c]
  · constructor
    · by_contra hc
      have hc : c < -10 := lt_of_not_ge hc
      have h3 := mul_nonpos_of_nonpos_of_nonneg (show c ≤ 0 by linarith) (sq_nonneg c)
      nlinarith [sq_nonneg c]
    · by_contra hc
      have hc : 10 < c := lt_of_not_ge hc
      have hm := mul_nonneg (sq_nonneg c) (show 0 ≤ 5*c-9 by linarith)
      nlinarith

#print axioms p6_real_root_bounds
end N6.Even
