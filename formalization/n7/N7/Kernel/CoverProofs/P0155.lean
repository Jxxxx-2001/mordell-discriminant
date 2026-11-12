import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.PositiveGroups.G0050
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1994 : BoxMajorant Geometry.b1994 := by
  exact PositiveLeaves.L551.bound

theorem bound1993 : BoxMajorant Geometry.b1993 := by
  exact PositiveLeaves.L552.bound

theorem bound1371 : BoxMajorant Geometry.b1371 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1371.Widths)
  · have he : Geometry.b1371.half 2 false=Geometry.b1993 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1993
  · have he : Geometry.b1371.half 2 true=Geometry.b1994 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1994

end N7.Kernel.Cover
