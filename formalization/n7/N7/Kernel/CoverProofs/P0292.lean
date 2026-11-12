import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0250
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3086 : BoxMajorant Geometry.b3086 := by
  exact PositiveLeaves.L957.bound

theorem bound3085 : BoxMajorant Geometry.b3085 := by
  exact PositiveLeaves.L958.bound

theorem bound2687 : BoxMajorant Geometry.b2687 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2687.Widths)
  · have he : Geometry.b2687.half 2 false=Geometry.b3085 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3085
  · have he : Geometry.b2687.half 2 true=Geometry.b3086 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3086

end N7.Kernel.Cover
