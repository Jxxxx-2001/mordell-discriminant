import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.PositiveGroups.G0286
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3150 : BoxMajorant Geometry.b3150 := by
  exact PositiveLeaves.L482.bound

theorem bound3149 : BoxMajorant Geometry.b3149 := by
  exact PositiveLeaves.L483.bound

theorem bound2757 : BoxMajorant Geometry.b2757 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2757.Widths)
  · have he : Geometry.b2757.half 2 false=Geometry.b3149 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3149
  · have he : Geometry.b2757.half 2 true=Geometry.b3150 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3150

end N7.Kernel.Cover
