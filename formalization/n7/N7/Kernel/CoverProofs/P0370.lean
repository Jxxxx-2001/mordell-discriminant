import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.PositiveGroups.G0423
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5172 : BoxMajorant Geometry.b5172 := by
  exact PositiveLeaves.L2046.bound

theorem bound5171 : BoxMajorant Geometry.b5171 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5171 2 (by decide +kernel) x hx hd ho).elim

theorem bound4841 : BoxMajorant Geometry.b4841 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4841.Widths)
  · have he : Geometry.b4841.half 0 false=Geometry.b5171 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5171
  · have he : Geometry.b4841.half 0 true=Geometry.b5172 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5172

end N7.Kernel.Cover
