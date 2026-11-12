import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.PositiveGroups.G0311
import N7.Kernel.PositiveGroups.G0337
import N7.Kernel.PositiveGroups.G0338
import N7.Kernel.PositiveGroups.G0366
import N7.Kernel.PositiveGroups.G0367
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4624 : BoxMajorant Geometry.b4624 := by
  exact PositiveLeaves.L1600.bound

theorem bound4623 : BoxMajorant Geometry.b4623 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4623 2 (by decide +kernel) x hx hd ho).elim

theorem bound4362 : BoxMajorant Geometry.b4362 := by
  exact PositiveLeaves.L1599.bound

theorem bound4361 : BoxMajorant Geometry.b4361 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4361.Widths)
  · have he : Geometry.b4361.half 1 false=Geometry.b4623 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4623
  · have he : Geometry.b4361.half 1 true=Geometry.b4624 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4624

theorem bound4360 : BoxMajorant Geometry.b4360 := by
  exact PositiveLeaves.L1603.bound

theorem bound4359 : BoxMajorant Geometry.b4359 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4359 2 (by decide +kernel) x hx hd ho).elim

theorem bound4358 : BoxMajorant Geometry.b4358 := by
  exact PositiveLeaves.L1607.bound

theorem bound4357 : BoxMajorant Geometry.b4357 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4357 2 (by decide +kernel) x hx hd ho).elim

theorem bound4010 : BoxMajorant Geometry.b4010 := by
  exact PositiveLeaves.L1598.bound

theorem bound4009 : BoxMajorant Geometry.b4009 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4009.Widths)
  · have he : Geometry.b4009.half 0 false=Geometry.b4361 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4361
  · have he : Geometry.b4009.half 0 true=Geometry.b4362 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4362

theorem bound4008 : BoxMajorant Geometry.b4008 := by
  exact PositiveLeaves.L1602.bound

theorem bound4007 : BoxMajorant Geometry.b4007 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4007.Widths)
  · have he : Geometry.b4007.half 0 false=Geometry.b4359 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4359
  · have he : Geometry.b4007.half 0 true=Geometry.b4360 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4360

theorem bound4006 : BoxMajorant Geometry.b4006 := by
  exact PositiveLeaves.L1605.bound

theorem bound4005 : BoxMajorant Geometry.b4005 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4005 2 (by decide +kernel) x hx hd ho).elim

theorem bound4004 : BoxMajorant Geometry.b4004 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4004.Widths)
  · have he : Geometry.b4004.half 0 false=Geometry.b4357 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4357
  · have he : Geometry.b4004.half 0 true=Geometry.b4358 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4358

theorem bound4003 : BoxMajorant Geometry.b4003 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4003 2 (by decide +kernel) x hx hd ho).elim

theorem bound3632 : BoxMajorant Geometry.b3632 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3632.Widths)
  · have he : Geometry.b3632.half 2 false=Geometry.b4009 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4009
  · have he : Geometry.b3632.half 2 true=Geometry.b4010 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4010

theorem bound3631 : BoxMajorant Geometry.b3631 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3631.Widths)
  · have he : Geometry.b3631.half 2 false=Geometry.b4007 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4007
  · have he : Geometry.b3631.half 2 true=Geometry.b4008 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4008

theorem bound3630 : BoxMajorant Geometry.b3630 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3630.Widths)
  · have he : Geometry.b3630.half 2 false=Geometry.b4005 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4005
  · have he : Geometry.b3630.half 2 true=Geometry.b4006 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4006

theorem bound3629 : BoxMajorant Geometry.b3629 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3629.Widths)
  · have he : Geometry.b3629.half 2 false=Geometry.b4003 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4003
  · have he : Geometry.b3629.half 2 true=Geometry.b4004 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4004

theorem bound3358 : BoxMajorant Geometry.b3358 := by
  exact PositiveLeaves.L1597.bound

theorem bound3357 : BoxMajorant Geometry.b3357 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3357.Widths)
  · have he : Geometry.b3357.half 1 false=Geometry.b3631 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3631
  · have he : Geometry.b3357.half 1 true=Geometry.b3632 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3632

theorem bound3356 : BoxMajorant Geometry.b3356 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3356.Widths)
  · have he : Geometry.b3356.half 1 false=Geometry.b3629 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3629
  · have he : Geometry.b3356.half 1 true=Geometry.b3630 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3630

theorem bound3355 : BoxMajorant Geometry.b3355 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3355 2 (by decide +kernel) x hx hd ho).elim

theorem bound3014 : BoxMajorant Geometry.b3014 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3014.Widths)
  · have he : Geometry.b3014.half 0 false=Geometry.b3357 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3357
  · have he : Geometry.b3014.half 0 true=Geometry.b3358 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3358

theorem bound3013 : BoxMajorant Geometry.b3013 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3013.Widths)
  · have he : Geometry.b3013.half 0 false=Geometry.b3355 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3355
  · have he : Geometry.b3013.half 0 true=Geometry.b3356 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3356

theorem bound2621 : BoxMajorant Geometry.b2621 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2621.Widths)
  · have he : Geometry.b2621.half 2 false=Geometry.b3013 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3013
  · have he : Geometry.b2621.half 2 true=Geometry.b3014 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3014

end N7.Kernel.Cover
