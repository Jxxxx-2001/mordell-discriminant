import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0304
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3110 : BoxMajorant Geometry.b3110 := by
  exact PositiveLeaves.L895.bound

theorem bound3109 : BoxMajorant Geometry.b3109 := by
  exact PositiveLeaves.L896.bound

theorem bound2705 : BoxMajorant Geometry.b2705 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2705.Widths)
  · have he : Geometry.b2705.half 2 false=Geometry.b3109 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3109
  · have he : Geometry.b2705.half 2 true=Geometry.b3110 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3110

end N7.Kernel.Cover
