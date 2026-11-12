import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.PositiveGroups.G0285
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3176 : BoxMajorant Geometry.b3176 := by
  exact PositiveLeaves.L152.bound

theorem bound3175 : BoxMajorant Geometry.b3175 := by
  exact PositiveLeaves.L153.bound

theorem bound2775 : BoxMajorant Geometry.b2775 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2775.Widths)
  · have he : Geometry.b2775.half 2 false=Geometry.b3175 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3175
  · have he : Geometry.b2775.half 2 true=Geometry.b3176 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3176

end N7.Kernel.Cover
