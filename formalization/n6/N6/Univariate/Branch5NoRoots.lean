import N6.Univariate.Branch5NoRootsGround
import N6.Univariate.Soundness
namespace N6.Univariate.Branch5
theorem no_root (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 225) : eval p a ≠ 0 := by
  intro hp
  have hmem : (⟨0,225⟩ : Bounds).Mem a := by
    simpa [Bounds.Mem, Bounds.toInterval, Mordell.Interval.Mem] using ha
  have h := noRootsTree.sound p [] 0 ⟨0,225⟩ a noRootsChecked hmem hp
  norm_num [eval] at h
#print axioms no_root
end N6.Univariate.Branch5
