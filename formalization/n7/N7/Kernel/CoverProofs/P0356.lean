import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.PositiveGroups.G0453
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5554 : BoxMajorant Geometry.b5554 := by
  exact PositiveLeaves.L2620.bound

theorem bound5553 : BoxMajorant Geometry.b5553 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5553 2 (by decide +kernel) x hx hd ho).elim

theorem bound5460 : BoxMajorant Geometry.b5460 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5460.Widths)
  · have he : Geometry.b5460.half 0 false=Geometry.b5553 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5553
  · have he : Geometry.b5460.half 0 true=Geometry.b5554 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5554

theorem bound5459 : BoxMajorant Geometry.b5459 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5459 2 (by decide +kernel) x hx hd ho).elim

theorem bound5330 : BoxMajorant Geometry.b5330 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5330.Widths)
  · have he : Geometry.b5330.half 2 false=Geometry.b5459 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5459
  · have he : Geometry.b5330.half 2 true=Geometry.b5460 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5460

theorem bound5329 : BoxMajorant Geometry.b5329 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5329 2 (by decide +kernel) x hx hd ho).elim

theorem bound5148 : BoxMajorant Geometry.b5148 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5148.Widths)
  · have he : Geometry.b5148.half 1 false=Geometry.b5329 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5329
  · have he : Geometry.b5148.half 1 true=Geometry.b5330 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5330

theorem bound5147 : BoxMajorant Geometry.b5147 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5147 2 (by decide +kernel) x hx hd ho).elim

theorem bound4791 : BoxMajorant Geometry.b4791 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4791.Widths)
  · have he : Geometry.b4791.half 0 false=Geometry.b5147 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5147
  · have he : Geometry.b4791.half 0 true=Geometry.b5148 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5148

end N7.Kernel.Cover
