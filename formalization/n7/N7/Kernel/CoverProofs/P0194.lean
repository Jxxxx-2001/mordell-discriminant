import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.PositiveGroups.G0152
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2828 : BoxMajorant Geometry.b2828 := by
  exact PositiveLeaves.L2670.bound

theorem bound2827 : BoxMajorant Geometry.b2827 := by
  exact PositiveLeaves.L2671.bound

theorem bound2476 : BoxMajorant Geometry.b2476 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2476.Widths)
  · have he : Geometry.b2476.half 2 false=Geometry.b2827 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2827
  · have he : Geometry.b2476.half 2 true=Geometry.b2828 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2828

end N7.Kernel.Cover
