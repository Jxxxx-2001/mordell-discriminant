import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0096
import N7.Kernel.PositiveGroups.G0138
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2064 : BoxMajorant Geometry.b2064 := by
  exact PositiveLeaves.L63.bound

theorem bound2063 : BoxMajorant Geometry.b2063 := by
  exact PositiveLeaves.L64.bound

theorem bound2062 : BoxMajorant Geometry.b2062 := by
  exact PositiveLeaves.L65.bound

theorem bound2061 : BoxMajorant Geometry.b2061 := by
  exact PositiveLeaves.L66.bound

theorem bound1420 : BoxMajorant Geometry.b1420 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1420.Widths)
  · have he : Geometry.b1420.half 2 false=Geometry.b2063 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2063
  · have he : Geometry.b1420.half 2 true=Geometry.b2064 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2064

theorem bound1419 : BoxMajorant Geometry.b1419 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1419.Widths)
  · have he : Geometry.b1419.half 2 false=Geometry.b2061 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2061
  · have he : Geometry.b1419.half 2 true=Geometry.b2062 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2062

theorem bound1012 : BoxMajorant Geometry.b1012 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1012.Widths)
  · have he : Geometry.b1012.half 1 false=Geometry.b1419 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1419
  · have he : Geometry.b1012.half 1 true=Geometry.b1420 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1420

end N7.Kernel.Cover
