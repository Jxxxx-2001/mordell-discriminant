import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.PositiveGroups.G0309
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3164 : BoxMajorant Geometry.b3164 := by
  exact PositiveLeaves.L183.bound

theorem bound3163 : BoxMajorant Geometry.b3163 := by
  exact PositiveLeaves.L184.bound

theorem bound2766 : BoxMajorant Geometry.b2766 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2766.Widths)
  · have he : Geometry.b2766.half 2 false=Geometry.b3163 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3163
  · have he : Geometry.b2766.half 2 true=Geometry.b3164 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3164

end N7.Kernel.Cover
