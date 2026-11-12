import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0302
import N7.Kernel.PositiveGroups.G0303
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3128 : BoxMajorant Geometry.b3128 := by
  exact PositiveLeaves.L675.bound

theorem bound3127 : BoxMajorant Geometry.b3127 := by
  exact PositiveLeaves.L676.bound

theorem bound2736 : BoxMajorant Geometry.b2736 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2736.Widths)
  · have he : Geometry.b2736.half 2 false=Geometry.b3127 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3127
  · have he : Geometry.b2736.half 2 true=Geometry.b3128 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3128

end N7.Kernel.Cover
