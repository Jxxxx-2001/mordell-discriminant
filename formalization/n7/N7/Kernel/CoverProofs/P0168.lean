import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0063
import N7.Kernel.PositiveGroups.G0097
import N7.Kernel.PositiveGroups.G0139
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2058 : BoxMajorant Geometry.b2058 := by
  exact PositiveLeaves.L104.bound

theorem bound2057 : BoxMajorant Geometry.b2057 := by
  exact PositiveLeaves.L105.bound

theorem bound1416 : BoxMajorant Geometry.b1416 := by
  exact PositiveLeaves.L103.bound

theorem bound1415 : BoxMajorant Geometry.b1415 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1415.Widths)
  · have he : Geometry.b1415.half 2 false=Geometry.b2057 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2057
  · have he : Geometry.b1415.half 2 true=Geometry.b2058 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2058

theorem bound1008 : BoxMajorant Geometry.b1008 := by
  exact PositiveLeaves.L102.bound

theorem bound1007 : BoxMajorant Geometry.b1007 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1007.Widths)
  · have he : Geometry.b1007.half 1 false=Geometry.b1415 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1415
  · have he : Geometry.b1007.half 1 true=Geometry.b1416 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1416

theorem bound702 : BoxMajorant Geometry.b702 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b702.Widths)
  · have he : Geometry.b702.half 0 false=Geometry.b1007 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1007
  · have he : Geometry.b702.half 0 true=Geometry.b1008 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1008

end N7.Kernel.Cover
