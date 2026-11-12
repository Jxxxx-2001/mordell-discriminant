import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0251
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3088 : BoxMajorant Geometry.b3088 := by
  exact PositiveLeaves.L955.bound

theorem bound3087 : BoxMajorant Geometry.b3087 := by
  exact PositiveLeaves.L956.bound

theorem bound2688 : BoxMajorant Geometry.b2688 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2688.Widths)
  · have he : Geometry.b2688.half 2 false=Geometry.b3087 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3087
  · have he : Geometry.b2688.half 2 true=Geometry.b3088 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3088

end N7.Kernel.Cover
