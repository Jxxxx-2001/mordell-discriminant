import N6.Univariate.IntegerBranch4Checks
import N6.Univariate.IntegerSoundness
import N6.Univariate.Branch4Data
import N6.Univariate.Soundness
namespace N6.IntegerCover.Branch4
theorem p_binding (a : ℝ) : eval p a = (pden : ℝ)*N6.Univariate.eval N6.Univariate.Branch4.p a := by
  norm_num [eval, N6.Univariate.eval, p, pden, N6.Univariate.Branch4.p]
  <;> ring
theorem v_binding (a : ℝ) : eval v a = (vden : ℝ)*N6.Univariate.eval N6.Univariate.Branch4.v a := by
  norm_num [eval, N6.Univariate.eval, v, vden, N6.Univariate.Branch4.v]
  <;> ring
theorem root_value_bound (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 225)
    (hp : N6.Univariate.eval N6.Univariate.Branch4.p a = 0) :
    -(6 : ℝ)^12 < N6.Univariate.eval N6.Univariate.Branch4.v a ∧
      N6.Univariate.eval N6.Univariate.Branch4.v a < (6 : ℝ)^12 := by
  have hmem : (⟨0,225,1⟩ : Bounds).Mem a := by simpa [Bounds.Mem] using ha
  have hp' : eval p a = 0 := by rw [p_binding, hp, mul_zero]
  have h := tree.sound p v vden 2176782336 ⟨0,225,1⟩ a (by decide) checked hmem hp'
  rw [v_binding] at h
  have hd : (0 : ℝ) < vden := by exact_mod_cast vden_pos
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  norm_num only [Nat.reducePow]
  constructor <;> nlinarith [h.1, h.2]
#print axioms p_binding
#print axioms v_binding
#print axioms root_value_bound
end N6.IntegerCover.Branch4
