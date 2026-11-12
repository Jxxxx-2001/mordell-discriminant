import Eight.RootGeometry.Common

namespace MordellEight.RootGeometry

/-- Canonical ordering collapses the first two coordinates of B8 to their shared cut. -/
theorem B8_in_B1 {x : Fin 3 → ℝ}
    (hx : RootPartition.B8.Contains x) (hd : CanonicalDomain x) :
    RootPartition.B1.Contains x := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  norm_num [RootPartition.B8,Matrix.cons_val_two] at h0 h1 h2
  have hc : x 0 ≤ x 1 := hd.2
  intro i
  fin_cases i
  · norm_num [RootPartition.B1,Matrix.cons_val_two]
    constructor <;> linarith
  · exact hx 1
  · exact hx 2

/-- The expensive positive leaf for B8 can be replaced by the already assembled B1 bound. -/
theorem bound8_of_bound1 (h1 : BoxMajorant RootPartition.B1) :
    BoxMajorant RootPartition.B8 := by
  intro x hx hd
  exact h1 x (B8_in_B1 hx hd) hd

#print axioms bound8_of_bound1
end MordellEight.RootGeometry
