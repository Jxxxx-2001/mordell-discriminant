import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0250
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3084 : BoxMajorant Geometry.b3084 := by
  exact PositiveLeaves.L959.bound

theorem bound3083 : BoxMajorant Geometry.b3083 := by
  exact PositiveLeaves.L960.bound

theorem bound2686 : BoxMajorant Geometry.b2686 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2686.Widths)
  · have he : Geometry.b2686.half 2 false=Geometry.b3083 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3083
  · have he : Geometry.b2686.half 2 true=Geometry.b3084 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3084

end N7.Kernel.Cover
