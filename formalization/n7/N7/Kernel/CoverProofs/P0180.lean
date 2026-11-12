import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0138
import N7.Kernel.PositiveGroups.G0174
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2080 : BoxMajorant Geometry.b2080 := by
  exact PositiveLeaves.L36.bound

theorem bound2079 : BoxMajorant Geometry.b2079 := by
  exact PositiveLeaves.L37.bound

theorem bound1432 : BoxMajorant Geometry.b1432 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1432.Widths)
  · have he : Geometry.b1432.half 2 false=Geometry.b2079 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2079
  · have he : Geometry.b1432.half 2 true=Geometry.b2080 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2080

theorem bound1431 : BoxMajorant Geometry.b1431 := by
  exact PositiveLeaves.L38.bound

theorem bound1019 : BoxMajorant Geometry.b1019 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1019.Widths)
  · have he : Geometry.b1019.half 1 false=Geometry.b1431 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1431
  · have he : Geometry.b1019.half 1 true=Geometry.b1432 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1432

end N7.Kernel.Cover
