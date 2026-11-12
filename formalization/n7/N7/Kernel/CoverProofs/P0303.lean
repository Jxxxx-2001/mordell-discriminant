import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0280
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3108 : BoxMajorant Geometry.b3108 := by
  exact PositiveLeaves.L898.bound

theorem bound3107 : BoxMajorant Geometry.b3107 := by
  exact PositiveLeaves.L899.bound

theorem bound2703 : BoxMajorant Geometry.b2703 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2703.Widths)
  · have he : Geometry.b2703.half 2 false=Geometry.b3107 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3107
  · have he : Geometry.b2703.half 2 true=Geometry.b3108 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3108

end N7.Kernel.Cover
