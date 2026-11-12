import Eight.CoefficientBounds

namespace MordellEight
open Checks

def cubicQ (q : ℚ) : ℚ := 8*q^3+4*q^2-4*q-1
def rootIntervalCheck (l h : ℚ) : Bool :=
  decide (1/2≤l ∧ l≤h ∧ cubicQ l≤0 ∧ 0≤cubicQ h)

theorem cubicQ_real (q : ℚ) : (cubicQ q:ℝ)=cubic (q:ℝ) := by
  simp [cubicQ,cubic]

/-- Refine the existing algebraic constant, rather than choosing a new approximate root. -/
theorem rootIntervalCheck_sound (l h : ℚ) (hc : rootIntervalCheck l h=true) :
    (⟨l,h⟩ : QInterval).Contains alpha := by
  have he := of_decide_eq_true hc
  have hl : (1/2:ℝ)≤(l:ℝ) := by
    have h : ((1/2:ℚ):ℝ)≤(l:ℝ) := by exact_mod_cast he.1
    norm_num at h
    exact h
  have hh : (1/2:ℝ)≤(h:ℝ) := hl.trans (by exact_mod_cast he.2.1)
  have hcl : cubic (l:ℝ)≤0 := by rw [←cubicQ_real]; exact_mod_cast he.2.2.1
  have hch : 0≤cubic (h:ℝ) := by rw [←cubicQ_real]; exact_mod_cast he.2.2.2
  constructor
  · by_contra hn
    have hs := cubic_strict alpha_coarse.1.le (lt_of_not_ge hn)
    rw [alpha_equation] at hs
    exact (not_lt_of_ge hcl) hs
  · by_contra hn
    have hs := cubic_strict hh (lt_of_not_ge hn)
    rw [alpha_equation] at hs
    exact (not_lt_of_ge hch) hs

def alphaRefined : QInterval := ⟨623489801858733530525004884004/1000000000000000000000000000000,623489801858733530525004884005/1000000000000000000000000000000⟩

theorem alphaRefined_checked : rootIntervalCheck alphaRefined.lo alphaRefined.hi=true := by
  decide +kernel

theorem alphaRefined_sound : alphaRefined.Contains alpha :=
  rootIntervalCheck_sound _ _ alphaRefined_checked

end MordellEight
