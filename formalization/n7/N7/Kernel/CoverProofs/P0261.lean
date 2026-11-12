import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.PositiveGroups.G0260
import N7.Kernel.PositiveGroups.G0286
import N7.Kernel.PositiveGroups.G0287
import N7.Kernel.PositiveGroups.G0310
import N7.Kernel.PositiveGroups.G0311
import N7.Kernel.PositiveGroups.G0334
import N7.Kernel.PositiveGroups.G0335
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4984 : BoxMajorant Geometry.b4984 := by
  exact PositiveLeaves.L1568.bound

theorem bound4983 : BoxMajorant Geometry.b4983 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4983 2 (by decide +kernel) x hx hd ho).elim

theorem bound4982 : BoxMajorant Geometry.b4982 := by
  exact PositiveLeaves.L1572.bound

theorem bound4981 : BoxMajorant Geometry.b4981 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4981 2 (by decide +kernel) x hx hd ho).elim

theorem bound4980 : BoxMajorant Geometry.b4980 := by
  exact PositiveLeaves.L1574.bound

theorem bound4979 : BoxMajorant Geometry.b4979 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4979 2 (by decide +kernel) x hx hd ho).elim

theorem bound4632 : BoxMajorant Geometry.b4632 := by
  exact PositiveLeaves.L1567.bound

theorem bound4631 : BoxMajorant Geometry.b4631 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4631.Widths)
  · have he : Geometry.b4631.half 2 false=Geometry.b4983 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4983
  · have he : Geometry.b4631.half 2 true=Geometry.b4984 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4984

theorem bound4630 : BoxMajorant Geometry.b4630 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4630.Widths)
  · have he : Geometry.b4630.half 2 false=Geometry.b4981 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4981
  · have he : Geometry.b4630.half 2 true=Geometry.b4982 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4982

theorem bound4629 : BoxMajorant Geometry.b4629 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4629.Widths)
  · have he : Geometry.b4629.half 2 false=Geometry.b4979 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4979
  · have he : Geometry.b4629.half 2 true=Geometry.b4980 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4980

theorem bound4372 : BoxMajorant Geometry.b4372 := by
  exact PositiveLeaves.L1566.bound

theorem bound4371 : BoxMajorant Geometry.b4371 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4371.Widths)
  · have he : Geometry.b4371.half 1 false=Geometry.b4631 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4631
  · have he : Geometry.b4371.half 1 true=Geometry.b4632 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4632

theorem bound4370 : BoxMajorant Geometry.b4370 := by
  exact PositiveLeaves.L1571.bound

theorem bound4369 : BoxMajorant Geometry.b4369 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4369.Widths)
  · have he : Geometry.b4369.half 1 false=Geometry.b4629 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4629
  · have he : Geometry.b4369.half 1 true=Geometry.b4630 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4630

theorem bound4022 : BoxMajorant Geometry.b4022 := by
  exact PositiveLeaves.L1565.bound

theorem bound4021 : BoxMajorant Geometry.b4021 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4021.Widths)
  · have he : Geometry.b4021.half 0 false=Geometry.b4371 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4371
  · have he : Geometry.b4021.half 0 true=Geometry.b4372 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4372

theorem bound4020 : BoxMajorant Geometry.b4020 := by
  exact PositiveLeaves.L1570.bound

theorem bound4019 : BoxMajorant Geometry.b4019 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4019.Widths)
  · have he : Geometry.b4019.half 0 false=Geometry.b4369 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4369
  · have he : Geometry.b4019.half 0 true=Geometry.b4370 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4370

theorem bound3640 : BoxMajorant Geometry.b3640 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3640.Widths)
  · have he : Geometry.b3640.half 2 false=Geometry.b4021 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4021
  · have he : Geometry.b3640.half 2 true=Geometry.b4022 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4022

theorem bound3639 : BoxMajorant Geometry.b3639 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3639.Widths)
  · have he : Geometry.b3639.half 2 false=Geometry.b4019 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4019
  · have he : Geometry.b3639.half 2 true=Geometry.b4020 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4020

theorem bound3364 : BoxMajorant Geometry.b3364 := by
  exact PositiveLeaves.L1564.bound

theorem bound3363 : BoxMajorant Geometry.b3363 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3363.Widths)
  · have he : Geometry.b3363.half 1 false=Geometry.b3639 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3639
  · have he : Geometry.b3363.half 1 true=Geometry.b3640 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3640

theorem bound3020 : BoxMajorant Geometry.b3020 := by
  exact PositiveLeaves.L1563.bound

theorem bound3019 : BoxMajorant Geometry.b3019 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3019.Widths)
  · have he : Geometry.b3019.half 0 false=Geometry.b3363 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3363
  · have he : Geometry.b3019.half 0 true=Geometry.b3364 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3364

theorem bound2624 : BoxMajorant Geometry.b2624 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2624.Widths)
  · have he : Geometry.b2624.half 2 false=Geometry.b3019 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3019
  · have he : Geometry.b2624.half 2 true=Geometry.b3020 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3020

end N7.Kernel.Cover
