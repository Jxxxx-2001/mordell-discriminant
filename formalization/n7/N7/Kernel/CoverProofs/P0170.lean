import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.PositiveGroups.G0065
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1378 : BoxMajorant Geometry.b1378 := by
  exact PositiveLeaves.L521.bound

theorem bound1377 : BoxMajorant Geometry.b1377 := by
  exact PositiveLeaves.L522.bound

theorem bound982 : BoxMajorant Geometry.b982 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b982.Widths)
  · have he : Geometry.b982.half 1 false=Geometry.b1377 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1377
  · have he : Geometry.b982.half 1 true=Geometry.b1378 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1378

end N7.Kernel.Cover
