import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.PositiveGroups.G0256
import N7.Kernel.PositiveGroups.G0257
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3170 : BoxMajorant Geometry.b3170 := by
  exact PositiveLeaves.L164.bound

theorem bound3169 : BoxMajorant Geometry.b3169 := by
  exact PositiveLeaves.L165.bound

theorem bound2772 : BoxMajorant Geometry.b2772 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2772.Widths)
  · have he : Geometry.b2772.half 2 false=Geometry.b3169 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3169
  · have he : Geometry.b2772.half 2 true=Geometry.b3170 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3170

end N7.Kernel.Cover
