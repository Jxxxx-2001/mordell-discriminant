import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.PositiveGroups.G0050
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1992 : BoxMajorant Geometry.b1992 := by
  exact PositiveLeaves.L553.bound

theorem bound1991 : BoxMajorant Geometry.b1991 := by
  exact PositiveLeaves.L554.bound

theorem bound1370 : BoxMajorant Geometry.b1370 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1370.Widths)
  · have he : Geometry.b1370.half 2 false=Geometry.b1991 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1991
  · have he : Geometry.b1370.half 2 true=Geometry.b1992 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1992

end N7.Kernel.Cover
