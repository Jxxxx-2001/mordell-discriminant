import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.PositiveGroups.G0148
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3220 : BoxMajorant Geometry.b3220 := by
  exact PositiveLeaves.L2512.bound

theorem bound3219 : BoxMajorant Geometry.b3219 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3219 2 (by decide +kernel) x hx hd ho).elim

theorem bound2854 : BoxMajorant Geometry.b2854 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2854.Widths)
  · have he : Geometry.b2854.half 0 false=Geometry.b3219 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3219
  · have he : Geometry.b2854.half 0 true=Geometry.b3220 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3220

end N7.Kernel.Cover
