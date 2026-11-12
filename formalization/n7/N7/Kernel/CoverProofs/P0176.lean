import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0136
import N7.Kernel.PositiveGroups.G0137
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2070 : BoxMajorant Geometry.b2070 := by
  exact PositiveLeaves.L53.bound

theorem bound2069 : BoxMajorant Geometry.b2069 := by
  exact PositiveLeaves.L54.bound

theorem bound2068 : BoxMajorant Geometry.b2068 := by
  exact PositiveLeaves.L55.bound

theorem bound2067 : BoxMajorant Geometry.b2067 := by
  exact PositiveLeaves.L56.bound

theorem bound1424 : BoxMajorant Geometry.b1424 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1424.Widths)
  · have he : Geometry.b1424.half 2 false=Geometry.b2069 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2069
  · have he : Geometry.b1424.half 2 true=Geometry.b2070 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2070

theorem bound1423 : BoxMajorant Geometry.b1423 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1423.Widths)
  · have he : Geometry.b1423.half 2 false=Geometry.b2067 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2067
  · have he : Geometry.b1423.half 2 true=Geometry.b2068 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2068

theorem bound1015 : BoxMajorant Geometry.b1015 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1015.Widths)
  · have he : Geometry.b1015.half 1 false=Geometry.b1423 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1423
  · have he : Geometry.b1015.half 1 true=Geometry.b1424 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1424

end N7.Kernel.Cover
