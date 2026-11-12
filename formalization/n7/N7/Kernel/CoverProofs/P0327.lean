import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.PositiveGroups.G0258
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3166 : BoxMajorant Geometry.b3166 := by
  exact PositiveLeaves.L180.bound

theorem bound3165 : BoxMajorant Geometry.b3165 := by
  exact PositiveLeaves.L181.bound

theorem bound2768 : BoxMajorant Geometry.b2768 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2768.Widths)
  · have he : Geometry.b2768.half 2 false=Geometry.b3165 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3165
  · have he : Geometry.b2768.half 2 true=Geometry.b3166 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3166

end N7.Kernel.Cover
