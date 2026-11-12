import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.PositiveGroups.G0422
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4846 : BoxMajorant Geometry.b4846 := by
  exact PositiveLeaves.L2039.bound

theorem bound4845 : BoxMajorant Geometry.b4845 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4845 2 (by decide +kernel) x hx hd ho).elim

theorem bound4536 : BoxMajorant Geometry.b4536 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4536.Widths)
  · have he : Geometry.b4536.half 2 false=Geometry.b4845 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4845
  · have he : Geometry.b4536.half 2 true=Geometry.b4846 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4846

end N7.Kernel.Cover
