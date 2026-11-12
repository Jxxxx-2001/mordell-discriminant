import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.PositiveGroups.G0266
import N7.Kernel.PositiveGroups.G0267
import N7.Kernel.PositiveGroups.G0296
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4516 : BoxMajorant Geometry.b4516 := by
  exact PositiveLeaves.L2175.bound

theorem bound4515 : BoxMajorant Geometry.b4515 := by
  exact PositiveLeaves.L2176.bound

theorem bound4212 : BoxMajorant Geometry.b4212 := by
  exact PositiveLeaves.L2174.bound

theorem bound4211 : BoxMajorant Geometry.b4211 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4211.Widths)
  · have he : Geometry.b4211.half 1 false=Geometry.b4515 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4515
  · have he : Geometry.b4211.half 1 true=Geometry.b4516 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4516

theorem bound3824 : BoxMajorant Geometry.b3824 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3824.Widths)
  · have he : Geometry.b3824.half 0 false=Geometry.b4211 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4211
  · have he : Geometry.b3824.half 0 true=Geometry.b4212 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4212

theorem bound3823 : BoxMajorant Geometry.b3823 := by
  exact PositiveLeaves.L2177.bound

theorem bound3521 : BoxMajorant Geometry.b3521 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3521.Widths)
  · have he : Geometry.b3521.half 2 false=Geometry.b3823 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3823
  · have he : Geometry.b3521.half 2 true=Geometry.b3824 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3824

end N7.Kernel.Cover
