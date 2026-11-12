import Eight.LogTangent
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace MordellEight
open Set

private noncomputable def cubicLogGap (y : ℝ) : ℝ :=
  y-y^2/2+y^3/3-Real.log (1+y)

private theorem cubicLogGap_hasDerivAt (s : ℝ) (hs : 0 < 1+s) :
    HasDerivAt cubicLogGap (s^3/(1+s)) s := by
  have hi := hasDerivAt_id s
  have hp : HasDerivAt (fun z : ℝ => z-z^2/2+z^3/3) (1-s+s^2) s := by
    convert (hi.sub ((hi.pow 2).div_const 2)).add ((hi.pow 3).div_const 3) using 1 <;>
      norm_num <;> ring
  have hlog : HasDerivAt (fun z : ℝ => Real.log (1+z)) (1/(1+s)) s :=
    (hi.const_add 1).log hs.ne'
  have he : 1-s+s^2-1/(1+s)=s^3/(1+s) := by
    field_simp [hs.ne']
    <;> ring
  simpa only [cubicLogGap,he] using hp.sub hlog

/-- The cubic Taylor polynomial is a global upper bound for log(1+y), y > -1. -/
theorem log_one_add_le_cubic {y : ℝ} (hy : -1 < y) :
    Real.log (1+y) ≤ y-y^2/2+y^3/3 := by
  have hgap : 0 ≤ cubicLogGap y := by
    by_cases hy0 : 0 ≤ y
    · have hm : MonotoneOn cubicLogGap (Icc (0:ℝ) y) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        · intro s hs
          exact (cubicLogGap_hasDerivAt s (by linarith [hs.1])).continuousAt.continuousWithinAt
        · intro s hs
          have hs' : s ∈ Icc (0:ℝ) y := interior_subset hs
          exact (cubicLogGap_hasDerivAt s (by linarith [hs'.1])).differentiableAt.differentiableWithinAt
        · intro s hs
          have hs' : s ∈ Icc (0:ℝ) y := interior_subset hs
          have hp : 0 < 1+s := by linarith [hs'.1]
          rw [(cubicLogGap_hasDerivAt s hp).deriv]
          exact div_nonneg (pow_nonneg hs'.1 3) hp.le
      have h := hm ⟨le_rfl,hy0⟩ ⟨hy0,le_rfl⟩ hy0
      simpa [cubicLogGap] using h
    · have hy0' : y ≤ 0 := le_of_not_ge hy0
      have hm : AntitoneOn cubicLogGap (Icc y (0:ℝ)) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        · intro s hs
          exact (cubicLogGap_hasDerivAt s (by linarith [hs.1])).continuousAt.continuousWithinAt
        · intro s hs
          have hs' : s ∈ Icc y (0:ℝ) := interior_subset hs
          exact (cubicLogGap_hasDerivAt s (by linarith [hs'.1])).differentiableAt.differentiableWithinAt
        · intro s hs
          have hs' : s ∈ Icc y (0:ℝ) := interior_subset hs
          have hp : 0 < 1+s := by linarith [hs'.1]
          rw [(cubicLogGap_hasDerivAt s hp).deriv]
          have hc : s^3 ≤ 0 := by
            nlinarith [mul_nonpos_of_nonpos_of_nonneg hs'.2 (sq_nonneg s)]
          exact div_nonpos_of_nonpos_of_nonneg hc hp.le
      have h := hm ⟨le_rfl,hy0'⟩ ⟨hy0',le_rfl⟩ hy0'
      simpa [cubicLogGap] using h
  dsimp [cubicLogGap] at hgap
  linarith

/-- A certified log bound at any positive scale gives a global cubic upper bound. -/
theorem log_le_cubic {d a l : ℝ} (hd : 0 < d) (ha : 0 < a)
    (hl : Real.log a ≤ l) :
    Real.log d ≤ l+(d/a-1)-(d/a-1)^2/2+(d/a-1)^3/3 := by
  have hpos : 0 < d/a := div_pos hd ha
  have h := log_one_add_le_cubic (y := d/a-1) (by linarith)
  have he : 1+(d/a-1)=d/a := by ring
  rw [he,Real.log_div hd.ne' ha.ne'] at h
  linarith

#print axioms log_le_cubic
end MordellEight

