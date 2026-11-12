import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.PositiveGroups.G0422
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5170 : BoxMajorant Geometry.b5170 := by
  exact PositiveLeaves.L2049.bound

theorem bound5169 : BoxMajorant Geometry.b5169 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5169 2 (by decide +kernel) x hx hd ho).elim

theorem bound4839 : BoxMajorant Geometry.b4839 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4839.Widths)
  · have he : Geometry.b4839.half 0 false=Geometry.b5169 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5169
  · have he : Geometry.b4839.half 0 true=Geometry.b5170 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5170

end N7.Kernel.Cover
