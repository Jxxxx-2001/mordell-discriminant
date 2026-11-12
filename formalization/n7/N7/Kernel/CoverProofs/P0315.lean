import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0326
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3132 : BoxMajorant Geometry.b3132 := by
  exact PositiveLeaves.L669.bound

theorem bound3131 : BoxMajorant Geometry.b3131 := by
  exact PositiveLeaves.L670.bound

theorem bound2738 : BoxMajorant Geometry.b2738 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2738.Widths)
  · have he : Geometry.b2738.half 2 false=Geometry.b3131 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3131
  · have he : Geometry.b2738.half 2 true=Geometry.b3132 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3132

end N7.Kernel.Cover
