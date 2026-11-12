import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0441
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5408 : BoxMajorant Geometry.b5408 := by
  exact PositiveLeaves.L2891.bound

theorem bound5407 : BoxMajorant Geometry.b5407 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5407 2 (by decide +kernel) x hx hd ho).elim

theorem bound5284 : BoxMajorant Geometry.b5284 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5284.Widths)
  · have he : Geometry.b5284.half 2 false=Geometry.b5407 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5407
  · have he : Geometry.b5284.half 2 true=Geometry.b5408 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5408

end N7.Kernel.Cover
