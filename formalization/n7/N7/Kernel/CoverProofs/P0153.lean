import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.PositiveGroups.G0049
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1990 : BoxMajorant Geometry.b1990 := by
  exact PositiveLeaves.L555.bound

theorem bound1989 : BoxMajorant Geometry.b1989 := by
  exact PositiveLeaves.L556.bound

theorem bound1369 : BoxMajorant Geometry.b1369 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1369.Widths)
  · have he : Geometry.b1369.half 2 false=Geometry.b1989 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1989
  · have he : Geometry.b1369.half 2 true=Geometry.b1990 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1990

end N7.Kernel.Cover
