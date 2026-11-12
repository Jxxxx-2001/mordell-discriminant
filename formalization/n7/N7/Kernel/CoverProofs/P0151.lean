import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.PositiveGroups.G0078
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1986 : BoxMajorant Geometry.b1986 := by
  exact PositiveLeaves.L560.bound

theorem bound1985 : BoxMajorant Geometry.b1985 := by
  exact PositiveLeaves.L561.bound

theorem bound1367 : BoxMajorant Geometry.b1367 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1367.Widths)
  · have he : Geometry.b1367.half 2 false=Geometry.b1985 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1985
  · have he : Geometry.b1367.half 2 true=Geometry.b1986 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1986

end N7.Kernel.Cover
