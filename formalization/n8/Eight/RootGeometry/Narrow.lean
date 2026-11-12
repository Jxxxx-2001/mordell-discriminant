import Eight.RootGeometry.Common

namespace MordellEight.RootGeometry

/-- Raise the second coordinate's lower face to the first coordinate's lower face. -/
def narrowBox (b : ClosedBox 3) : ClosedBox 3 := b.right 1 (b.lo 0)

/-- The canonical ordering makes the removed region irrelevant, including its cut face. -/
theorem narrow_contains (b : ClosedBox 3) {x : Fin 3 → ℝ}
    (hx : b.Contains x) (hd : CanonicalDomain x) : (narrowBox b).Contains x := by
  intro i
  fin_cases i
  · simpa [narrowBox,ClosedBox.right] using hx 0
  · change (b.lo 0 : ℝ) ≤ x 1 ∧ x 1 ≤ (b.hi 1 : ℝ)
    exact ⟨le_trans (hx 0).1 hd.2,(hx 1).2⟩
  · simpa [narrowBox,ClosedBox.right] using hx 2

theorem majorant_of_narrow (b : ClosedBox 3) (h : BoxMajorant (narrowBox b)) :
    BoxMajorant b := by
  intro x hx hd
  exact h x (narrow_contains b hx hd) hd

#print axioms narrow_contains
#print axioms majorant_of_narrow
end MordellEight.RootGeometry
