import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.PositiveGroups.G0460
import N7.Kernel.PositiveGroups.G0461
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5094 : BoxMajorant Geometry.b5094 := by
  exact PositiveLeaves.L209.bound

theorem bound5093 : BoxMajorant Geometry.b5093 := by
  exact PositiveLeaves.L210.bound

theorem bound4707 : BoxMajorant Geometry.b4707 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4707.Widths)
  · have he : Geometry.b4707.half 2 false=Geometry.b5093 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5093
  · have he : Geometry.b4707.half 2 true=Geometry.b5094 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5094

end N7.Kernel.Cover
