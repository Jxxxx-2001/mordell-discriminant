import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.PositiveGroups.G0060
import N7.Kernel.PositiveGroups.G0061
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1442 : BoxMajorant Geometry.b1442 := by
  exact PositiveLeaves.L6.bound

theorem bound1441 : BoxMajorant Geometry.b1441 := by
  exact PositiveLeaves.L7.bound

theorem bound1026 : BoxMajorant Geometry.b1026 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1026.Widths)
  · have he : Geometry.b1026.half 1 false=Geometry.b1441 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1441
  · have he : Geometry.b1026.half 1 true=Geometry.b1442 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1442

end N7.Kernel.Cover
