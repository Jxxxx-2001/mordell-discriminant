import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0276
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3118 : BoxMajorant Geometry.b3118 := by
  exact PositiveLeaves.L688.bound

theorem bound3117 : BoxMajorant Geometry.b3117 := by
  exact PositiveLeaves.L689.bound

theorem bound2730 : BoxMajorant Geometry.b2730 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2730.Widths)
  · have he : Geometry.b2730.half 2 false=Geometry.b3117 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3117
  · have he : Geometry.b2730.half 2 true=Geometry.b3118 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3118

end N7.Kernel.Cover
