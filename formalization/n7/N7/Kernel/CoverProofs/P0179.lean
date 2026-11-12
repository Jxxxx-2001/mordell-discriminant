import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0137
import N7.Kernel.PositiveGroups.G0174
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2078 : BoxMajorant Geometry.b2078 := by
  exact PositiveLeaves.L42.bound

theorem bound2077 : BoxMajorant Geometry.b2077 := by
  exact PositiveLeaves.L43.bound

theorem bound1430 : BoxMajorant Geometry.b1430 := by
  exact PositiveLeaves.L41.bound

theorem bound1429 : BoxMajorant Geometry.b1429 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1429.Widths)
  · have he : Geometry.b1429.half 2 false=Geometry.b2077 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2077
  · have he : Geometry.b1429.half 2 true=Geometry.b2078 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2078

theorem bound1018 : BoxMajorant Geometry.b1018 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1018.Widths)
  · have he : Geometry.b1018.half 1 false=Geometry.b1429 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1429
  · have he : Geometry.b1018.half 1 true=Geometry.b1430 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1430

end N7.Kernel.Cover
