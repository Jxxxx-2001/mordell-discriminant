import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0173
import N7.Kernel.PositiveGroups.G0216
import N7.Kernel.PositiveGroups.G0217
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2084 : BoxMajorant Geometry.b2084 := by
  exact PositiveLeaves.L32.bound

theorem bound2083 : BoxMajorant Geometry.b2083 := by
  exact PositiveLeaves.L33.bound

theorem bound2082 : BoxMajorant Geometry.b2082 := by
  exact PositiveLeaves.L34.bound

theorem bound2081 : BoxMajorant Geometry.b2081 := by
  exact PositiveLeaves.L35.bound

theorem bound1434 : BoxMajorant Geometry.b1434 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1434.Widths)
  · have he : Geometry.b1434.half 2 false=Geometry.b2083 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2083
  · have he : Geometry.b1434.half 2 true=Geometry.b2084 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2084

theorem bound1433 : BoxMajorant Geometry.b1433 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1433.Widths)
  · have he : Geometry.b1433.half 2 false=Geometry.b2081 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2081
  · have he : Geometry.b1433.half 2 true=Geometry.b2082 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2082

theorem bound1020 : BoxMajorant Geometry.b1020 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1020.Widths)
  · have he : Geometry.b1020.half 1 false=Geometry.b1433 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1433
  · have he : Geometry.b1020.half 1 true=Geometry.b1434 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1434

end N7.Kernel.Cover
