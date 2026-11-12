import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.PositiveGroups.G0379
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5166 : BoxMajorant Geometry.b5166 := by
  exact PositiveLeaves.L2070.bound

theorem bound5165 : BoxMajorant Geometry.b5165 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5165 2 (by decide +kernel) x hx hd ho).elim

theorem bound4827 : BoxMajorant Geometry.b4827 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4827.Widths)
  · have he : Geometry.b4827.half 0 false=Geometry.b5165 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5165
  · have he : Geometry.b4827.half 0 true=Geometry.b5166 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5166

end N7.Kernel.Cover
