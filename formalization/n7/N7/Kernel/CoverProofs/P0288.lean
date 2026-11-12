import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0387
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5486 : BoxMajorant Geometry.b5486 := by
  exact PositiveLeaves.L1313.bound

theorem bound5485 : BoxMajorant Geometry.b5485 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5485 2 (by decide +kernel) x hx hd ho).elim

theorem bound5356 : BoxMajorant Geometry.b5356 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5356.Widths)
  · have he : Geometry.b5356.half 2 false=Geometry.b5485 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5485
  · have he : Geometry.b5356.half 2 true=Geometry.b5486 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5486

end N7.Kernel.Cover
