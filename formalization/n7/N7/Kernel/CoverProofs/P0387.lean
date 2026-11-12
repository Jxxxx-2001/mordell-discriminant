import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.PositiveGroups.G0432
import N7.Kernel.PositiveGroups.G0433
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5054 : BoxMajorant Geometry.b5054 := by
  exact PositiveLeaves.L456.bound

theorem bound5053 : BoxMajorant Geometry.b5053 := by
  exact PositiveLeaves.L457.bound

theorem bound5052 : BoxMajorant Geometry.b5052 := by
  exact PositiveLeaves.L458.bound

theorem bound5051 : BoxMajorant Geometry.b5051 := by
  exact PositiveLeaves.L459.bound

theorem bound4680 : BoxMajorant Geometry.b4680 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4680.Widths)
  · have he : Geometry.b4680.half 2 false=Geometry.b5053 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5053
  · have he : Geometry.b4680.half 2 true=Geometry.b5054 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5054

theorem bound4679 : BoxMajorant Geometry.b4679 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4679.Widths)
  · have he : Geometry.b4679.half 2 false=Geometry.b5051 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5051
  · have he : Geometry.b4679.half 2 true=Geometry.b5052 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5052

theorem bound4413 : BoxMajorant Geometry.b4413 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4413.Widths)
  · have he : Geometry.b4413.half 1 false=Geometry.b4679 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4679
  · have he : Geometry.b4413.half 1 true=Geometry.b4680 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4680

end N7.Kernel.Cover
