import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0269
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5458 : BoxMajorant Geometry.b5458 := by
  exact PositiveLeaves.L2653.bound

theorem bound5457 : BoxMajorant Geometry.b5457 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5457 2 (by decide +kernel) x hx hd ho).elim

theorem bound5326 : BoxMajorant Geometry.b5326 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5326.Widths)
  · have he : Geometry.b5326.half 2 false=Geometry.b5457 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5457
  · have he : Geometry.b5326.half 2 true=Geometry.b5458 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5458

theorem bound5325 : BoxMajorant Geometry.b5325 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5325 0 (by decide +kernel) x hx hd ho).elim

theorem bound5144 : BoxMajorant Geometry.b5144 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5144 0 (by decide +kernel) x hx hd ho).elim

theorem bound5143 : BoxMajorant Geometry.b5143 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5143.Widths)
  · have he : Geometry.b5143.half 1 false=Geometry.b5325 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5325
  · have he : Geometry.b5143.half 1 true=Geometry.b5326 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5326

theorem bound4788 : BoxMajorant Geometry.b4788 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4788.Widths)
  · have he : Geometry.b4788.half 0 false=Geometry.b5143 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5143
  · have he : Geometry.b4788.half 0 true=Geometry.b5144 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5144

theorem bound4787 : BoxMajorant Geometry.b4787 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4787 2 (by decide +kernel) x hx hd ho).elim

theorem bound4496 : BoxMajorant Geometry.b4496 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4496.Widths)
  · have he : Geometry.b4496.half 2 false=Geometry.b4787 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4787
  · have he : Geometry.b4496.half 2 true=Geometry.b4788 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4788

theorem bound4495 : BoxMajorant Geometry.b4495 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4495 0 (by decide +kernel) x hx hd ho).elim

theorem bound4194 : BoxMajorant Geometry.b4194 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4194 0 (by decide +kernel) x hx hd ho).elim

theorem bound4193 : BoxMajorant Geometry.b4193 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4193.Widths)
  · have he : Geometry.b4193.half 1 false=Geometry.b4495 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4495
  · have he : Geometry.b4193.half 1 true=Geometry.b4496 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4496

theorem bound3788 : BoxMajorant Geometry.b3788 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3788.Widths)
  · have he : Geometry.b3788.half 0 false=Geometry.b4193 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4193
  · have he : Geometry.b3788.half 0 true=Geometry.b4194 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4194

theorem bound3787 : BoxMajorant Geometry.b3787 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3787 2 (by decide +kernel) x hx hd ho).elim

theorem bound3490 : BoxMajorant Geometry.b3490 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3490.Widths)
  · have he : Geometry.b3490.half 2 false=Geometry.b3787 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3787
  · have he : Geometry.b3490.half 2 true=Geometry.b3788 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3788

theorem bound3489 : BoxMajorant Geometry.b3489 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3489 0 (by decide +kernel) x hx hd ho).elim

theorem bound3206 : BoxMajorant Geometry.b3206 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3206 0 (by decide +kernel) x hx hd ho).elim

theorem bound3205 : BoxMajorant Geometry.b3205 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3205.Widths)
  · have he : Geometry.b3205.half 1 false=Geometry.b3489 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3489
  · have he : Geometry.b3205.half 1 true=Geometry.b3490 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3490

theorem bound2830 : BoxMajorant Geometry.b2830 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2830.Widths)
  · have he : Geometry.b2830.half 0 false=Geometry.b3205 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3205
  · have he : Geometry.b2830.half 0 true=Geometry.b3206 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3206

theorem bound2829 : BoxMajorant Geometry.b2829 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2829 2 (by decide +kernel) x hx hd ho).elim

theorem bound2480 : BoxMajorant Geometry.b2480 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2480.Widths)
  · have he : Geometry.b2480.half 2 false=Geometry.b2829 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2829
  · have he : Geometry.b2480.half 2 true=Geometry.b2830 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2830

theorem bound2479 : BoxMajorant Geometry.b2479 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2479 0 (by decide +kernel) x hx hd ho).elim

theorem bound2120 : BoxMajorant Geometry.b2120 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2120 0 (by decide +kernel) x hx hd ho).elim

theorem bound2119 : BoxMajorant Geometry.b2119 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2119.Widths)
  · have he : Geometry.b2119.half 1 false=Geometry.b2479 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2479
  · have he : Geometry.b2119.half 1 true=Geometry.b2480 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2480

theorem bound1472 : BoxMajorant Geometry.b1472 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1472.Widths)
  · have he : Geometry.b1472.half 0 false=Geometry.b2119 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2119
  · have he : Geometry.b1472.half 0 true=Geometry.b2120 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2120

theorem bound1471 : BoxMajorant Geometry.b1471 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1471 2 (by decide +kernel) x hx hd ho).elim

theorem bound1048 : BoxMajorant Geometry.b1048 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1048.Widths)
  · have he : Geometry.b1048.half 2 false=Geometry.b1471 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1471
  · have he : Geometry.b1048.half 2 true=Geometry.b1472 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1472

theorem bound1047 : BoxMajorant Geometry.b1047 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1047 0 (by decide +kernel) x hx hd ho).elim

theorem bound760 : BoxMajorant Geometry.b760 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b760 0 (by decide +kernel) x hx hd ho).elim

theorem bound759 : BoxMajorant Geometry.b759 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b759.Widths)
  · have he : Geometry.b759.half 1 false=Geometry.b1047 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1047
  · have he : Geometry.b759.half 1 true=Geometry.b1048 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1048

theorem bound487 : BoxMajorant Geometry.b487 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b487.Widths)
  · have he : Geometry.b487.half 0 false=Geometry.b759 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound759
  · have he : Geometry.b487.half 0 true=Geometry.b760 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound760

end N7.Kernel.Cover
