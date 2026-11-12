import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.PositiveGroups.G0117
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3144 : BoxMajorant Geometry.b3144 := by
  exact PositiveLeaves.L538.bound

theorem bound3143 : BoxMajorant Geometry.b3143 := by
  exact PositiveLeaves.L539.bound

theorem bound2752 : BoxMajorant Geometry.b2752 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2752.Widths)
  · have he : Geometry.b2752.half 2 false=Geometry.b3143 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3143
  · have he : Geometry.b2752.half 2 true=Geometry.b3144 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3144

end N7.Kernel.Cover
