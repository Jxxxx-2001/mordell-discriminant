import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0300
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3120 : BoxMajorant Geometry.b3120 := by
  exact PositiveLeaves.L686.bound

theorem bound3119 : BoxMajorant Geometry.b3119 := by
  exact PositiveLeaves.L687.bound

theorem bound2731 : BoxMajorant Geometry.b2731 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2731.Widths)
  · have he : Geometry.b2731.half 2 false=Geometry.b3119 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3119
  · have he : Geometry.b2731.half 2 true=Geometry.b3120 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3120

end N7.Kernel.Cover
