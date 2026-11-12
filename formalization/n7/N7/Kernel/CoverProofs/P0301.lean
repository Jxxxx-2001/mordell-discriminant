import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0304
import N7.Kernel.PositiveGroups.G0305
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3104 : BoxMajorant Geometry.b3104 := by
  exact PositiveLeaves.L903.bound

theorem bound3103 : BoxMajorant Geometry.b3103 := by
  exact PositiveLeaves.L904.bound

theorem bound2701 : BoxMajorant Geometry.b2701 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2701.Widths)
  · have he : Geometry.b2701.half 2 false=Geometry.b3103 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3103
  · have he : Geometry.b2701.half 2 true=Geometry.b3104 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3104

end N7.Kernel.Cover
