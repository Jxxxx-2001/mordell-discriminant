import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0280
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3098 : BoxMajorant Geometry.b3098 := by
  exact PositiveLeaves.L918.bound

theorem bound3097 : BoxMajorant Geometry.b3097 := by
  exact PositiveLeaves.L919.bound

theorem bound2697 : BoxMajorant Geometry.b2697 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2697.Widths)
  · have he : Geometry.b2697.half 2 false=Geometry.b3097 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3097
  · have he : Geometry.b2697.half 2 true=Geometry.b3098 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3098

end N7.Kernel.Cover
