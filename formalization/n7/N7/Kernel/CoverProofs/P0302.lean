import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0305
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3106 : BoxMajorant Geometry.b3106 := by
  exact PositiveLeaves.L901.bound

theorem bound3105 : BoxMajorant Geometry.b3105 := by
  exact PositiveLeaves.L902.bound

theorem bound2702 : BoxMajorant Geometry.b2702 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2702.Widths)
  · have he : Geometry.b2702.half 2 false=Geometry.b3105 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3105
  · have he : Geometry.b2702.half 2 true=Geometry.b3106 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3106

end N7.Kernel.Cover
