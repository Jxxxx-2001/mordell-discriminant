import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.PositiveGroups.G0078
import N7.Kernel.PositiveGroups.G0079
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1988 : BoxMajorant Geometry.b1988 := by
  exact PositiveLeaves.L558.bound

theorem bound1987 : BoxMajorant Geometry.b1987 := by
  exact PositiveLeaves.L559.bound

theorem bound1368 : BoxMajorant Geometry.b1368 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1368.Widths)
  · have he : Geometry.b1368.half 2 false=Geometry.b1987 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1987
  · have he : Geometry.b1368.half 2 true=Geometry.b1988 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1988

end N7.Kernel.Cover
