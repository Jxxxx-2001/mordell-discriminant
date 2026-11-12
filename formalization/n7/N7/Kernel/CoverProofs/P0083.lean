import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.PositiveGroups.G0155
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3064 : BoxMajorant Geometry.b3064 := by
  exact PositiveLeaves.L1250.bound

theorem bound3063 : BoxMajorant Geometry.b3063 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3063 2 (by decide +kernel) x hx hd ho).elim

theorem bound2658 : BoxMajorant Geometry.b2658 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2658.Widths)
  · have he : Geometry.b2658.half 2 false=Geometry.b3063 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3063
  · have he : Geometry.b2658.half 2 true=Geometry.b3064 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3064

theorem bound2657 : BoxMajorant Geometry.b2657 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2657 0 (by decide +kernel) x hx hd ho).elim

theorem bound2285 : BoxMajorant Geometry.b2285 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2285.Widths)
  · have he : Geometry.b2285.half 1 false=Geometry.b2657 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2657
  · have he : Geometry.b2285.half 1 true=Geometry.b2658 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2658

end N7.Kernel.Cover
