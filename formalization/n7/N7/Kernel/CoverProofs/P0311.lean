import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0301
import N7.Kernel.PositiveGroups.G0302
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3124 : BoxMajorant Geometry.b3124 := by
  exact PositiveLeaves.L679.bound

theorem bound3123 : BoxMajorant Geometry.b3123 := by
  exact PositiveLeaves.L680.bound

theorem bound2734 : BoxMajorant Geometry.b2734 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2734.Widths)
  · have he : Geometry.b2734.half 2 false=Geometry.b3123 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3123
  · have he : Geometry.b2734.half 2 true=Geometry.b3124 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3124

end N7.Kernel.Cover
