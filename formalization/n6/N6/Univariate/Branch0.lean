import N6.Univariate.Branch0Checks
import N6.Univariate.Soundness
namespace N6.Univariate.Branch0
theorem root_value_bound (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 225) (hp : eval p a = 0) :
    -(6 : ℝ)^12 < eval v a ∧ eval v a < (6 : ℝ)^12 := by
  have hmem : (⟨0, 225⟩ : Bounds).Mem a := by
    simpa [Bounds.Mem, Bounds.toInterval, Mordell.Interval.Mem] using ha
  have h := tree.sound p v 2176782336 ⟨0, 225⟩ a checked hmem hp
  norm_num at h ⊢
  exact h
#print axioms root_value_bound
end N6.Univariate.Branch0
