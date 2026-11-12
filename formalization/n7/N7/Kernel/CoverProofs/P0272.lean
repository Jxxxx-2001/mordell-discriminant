import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.PositiveGroups.G0262
import N7.Kernel.PositiveGroups.G0288
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3616 : BoxMajorant Geometry.b3616 := by
  exact PositiveLeaves.L1654.bound

theorem bound3615 : BoxMajorant Geometry.b3615 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3615 2 (by decide +kernel) x hx hd ho).elim

theorem bound3344 : BoxMajorant Geometry.b3344 := by
  exact PositiveLeaves.L1653.bound

theorem bound3343 : BoxMajorant Geometry.b3343 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3343.Widths)
  · have he : Geometry.b3343.half 1 false=Geometry.b3615 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3615
  · have he : Geometry.b3343.half 1 true=Geometry.b3616 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3616

theorem bound3004 : BoxMajorant Geometry.b3004 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3004.Widths)
  · have he : Geometry.b3004.half 0 false=Geometry.b3343 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3343
  · have he : Geometry.b3004.half 0 true=Geometry.b3344 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3344

end N7.Kernel.Cover
