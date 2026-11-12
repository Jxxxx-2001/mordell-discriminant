import Eight.DyadicPilot
import Eight.RootPartition

namespace MordellEight.RootBounds.B31

/-- Canonical order places the entire physical part of B31 in the cached S6 pilot. -/
theorem majorant : BoxMajorant RootPartition.B31 := by
  let s := TensorPilotStages.S6.state.box
  let b := RootPartition.B31
  have hlo : ∀ i, s.lo i ≤ b.lo i ∨ (i = 1 ∧ s.lo i ≤ b.lo 0) := by dsimp only [s,b]; decide +kernel
  have hhi : ∀ i, b.hi i ≤ s.hi i := by dsimp only [s,b]; decide +kernel
  intro x hx hd
  refine DyadicPilot.majorant x ?_ hd
  intro i
  constructor
  · rcases hlo i with h | ⟨rfl,h⟩
    · exact le_trans (by exact_mod_cast h) (hx i).1
    · exact le_trans (by exact_mod_cast h) ((hx 0).1.trans hd.2)
  · exact le_trans (hx i).2 (by exact_mod_cast hhi i)

#print axioms majorant
end MordellEight.RootBounds.B31
