import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.PositiveGroups.G0284
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3174 : BoxMajorant Geometry.b3174 := by
  exact PositiveLeaves.L154.bound

theorem bound3173 : BoxMajorant Geometry.b3173 := by
  exact PositiveLeaves.L155.bound

theorem bound2774 : BoxMajorant Geometry.b2774 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2774.Widths)
  · have he : Geometry.b2774.half 2 false=Geometry.b3173 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3173
  · have he : Geometry.b2774.half 2 true=Geometry.b3174 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3174

end N7.Kernel.Cover
