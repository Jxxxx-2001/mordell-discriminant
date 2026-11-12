import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.PositiveGroups.G0443
import N7.Kernel.PositiveGroups.G0444
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5080 : BoxMajorant Geometry.b5080 := by
  exact PositiveLeaves.L256.bound

theorem bound5079 : BoxMajorant Geometry.b5079 := by
  exact PositiveLeaves.L257.bound

theorem bound4697 : BoxMajorant Geometry.b4697 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4697.Widths)
  · have he : Geometry.b4697.half 2 false=Geometry.b5079 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5079
  · have he : Geometry.b4697.half 2 true=Geometry.b5080 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5080

end N7.Kernel.Cover
