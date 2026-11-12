import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0454
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5452 : BoxMajorant Geometry.b5452 := by
  exact PositiveLeaves.L2797.bound

theorem bound5451 : BoxMajorant Geometry.b5451 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5451 2 (by decide +kernel) x hx hd ho).elim

theorem bound5320 : BoxMajorant Geometry.b5320 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5320.Widths)
  · have he : Geometry.b5320.half 2 false=Geometry.b5451 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5451
  · have he : Geometry.b5320.half 2 true=Geometry.b5452 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5452

theorem bound5319 : BoxMajorant Geometry.b5319 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5319 2 (by decide +kernel) x hx hd ho).elim

theorem bound5132 : BoxMajorant Geometry.b5132 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5132.Widths)
  · have he : Geometry.b5132.half 1 false=Geometry.b5319 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5319
  · have he : Geometry.b5132.half 1 true=Geometry.b5320 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5320

theorem bound5131 : BoxMajorant Geometry.b5131 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5131 2 (by decide +kernel) x hx hd ho).elim

theorem bound4751 : BoxMajorant Geometry.b4751 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4751.Widths)
  · have he : Geometry.b4751.half 0 false=Geometry.b5131 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5131
  · have he : Geometry.b4751.half 0 true=Geometry.b5132 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5132

end N7.Kernel.Cover
