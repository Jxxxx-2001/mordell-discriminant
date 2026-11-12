import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0300
import N7.Kernel.PositiveGroups.G0301
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3122 : BoxMajorant Geometry.b3122 := by
  exact PositiveLeaves.L684.bound

theorem bound3121 : BoxMajorant Geometry.b3121 := by
  exact PositiveLeaves.L685.bound

theorem bound2732 : BoxMajorant Geometry.b2732 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2732.Widths)
  · have he : Geometry.b2732.half 2 false=Geometry.b3121 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3121
  · have he : Geometry.b2732.half 2 true=Geometry.b3122 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3122

end N7.Kernel.Cover
