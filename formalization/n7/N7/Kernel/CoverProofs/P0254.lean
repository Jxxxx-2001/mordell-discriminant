import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverProofs.P0371
import N7.Kernel.PositiveGroups.G0288
import N7.Kernel.PositiveGroups.G0312
import N7.Kernel.PositiveGroups.G0339
import N7.Kernel.PositiveGroups.G0368
import N7.Kernel.PositiveGroups.G0369
import N7.Kernel.PositiveGroups.G0398
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4618 : BoxMajorant Geometry.b4618 := by
  exact PositiveLeaves.L1639.bound

theorem bound4616 : BoxMajorant Geometry.b4616 := by
  exact PositiveLeaves.L1646.bound

theorem bound4615 : BoxMajorant Geometry.b4615 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4615 2 (by decide +kernel) x hx hd ho).elim

theorem bound4350 : BoxMajorant Geometry.b4350 := by
  exact PositiveLeaves.L1638.bound

theorem bound4349 : BoxMajorant Geometry.b4349 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4349.Widths)
  · have he : Geometry.b4349.half 1 false=Geometry.b4617 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4617
  · have he : Geometry.b4349.half 1 true=Geometry.b4618 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4618

theorem bound4348 : BoxMajorant Geometry.b4348 := by
  exact PositiveLeaves.L1643.bound

theorem bound4347 : BoxMajorant Geometry.b4347 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4347 2 (by decide +kernel) x hx hd ho).elim

theorem bound4346 : BoxMajorant Geometry.b4346 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4346.Widths)
  · have he : Geometry.b4346.half 1 false=Geometry.b4615 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4615
  · have he : Geometry.b4346.half 1 true=Geometry.b4616 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4616

theorem bound4345 : BoxMajorant Geometry.b4345 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4345 2 (by decide +kernel) x hx hd ho).elim

theorem bound4344 : BoxMajorant Geometry.b4344 := by
  exact PositiveLeaves.L1649.bound

theorem bound4343 : BoxMajorant Geometry.b4343 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4343 2 (by decide +kernel) x hx hd ho).elim

theorem bound3992 : BoxMajorant Geometry.b3992 := by
  exact PositiveLeaves.L1637.bound

theorem bound3991 : BoxMajorant Geometry.b3991 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3991.Widths)
  · have he : Geometry.b3991.half 0 false=Geometry.b4349 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4349
  · have he : Geometry.b3991.half 0 true=Geometry.b4350 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4350

theorem bound3990 : BoxMajorant Geometry.b3990 := by
  exact PositiveLeaves.L1642.bound

theorem bound3989 : BoxMajorant Geometry.b3989 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3989.Widths)
  · have he : Geometry.b3989.half 0 false=Geometry.b4347 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4347
  · have he : Geometry.b3989.half 0 true=Geometry.b4348 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4348

theorem bound3988 : BoxMajorant Geometry.b3988 := by
  exact PositiveLeaves.L1645.bound

theorem bound3987 : BoxMajorant Geometry.b3987 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3987.Widths)
  · have he : Geometry.b3987.half 0 false=Geometry.b4345 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4345
  · have he : Geometry.b3987.half 0 true=Geometry.b4346 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4346

theorem bound3986 : BoxMajorant Geometry.b3986 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3986.Widths)
  · have he : Geometry.b3986.half 0 false=Geometry.b4343 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4343
  · have he : Geometry.b3986.half 0 true=Geometry.b4344 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4344

theorem bound3985 : BoxMajorant Geometry.b3985 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3985 2 (by decide +kernel) x hx hd ho).elim

theorem bound3622 : BoxMajorant Geometry.b3622 := by
  exact PositiveLeaves.L1636.bound

theorem bound3621 : BoxMajorant Geometry.b3621 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3621.Widths)
  · have he : Geometry.b3621.half 2 false=Geometry.b3991 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3991
  · have he : Geometry.b3621.half 2 true=Geometry.b3992 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3992

theorem bound3620 : BoxMajorant Geometry.b3620 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3620.Widths)
  · have he : Geometry.b3620.half 2 false=Geometry.b3989 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3989
  · have he : Geometry.b3620.half 2 true=Geometry.b3990 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3990

theorem bound3619 : BoxMajorant Geometry.b3619 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3619.Widths)
  · have he : Geometry.b3619.half 2 false=Geometry.b3987 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3987
  · have he : Geometry.b3619.half 2 true=Geometry.b3988 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3988

theorem bound3618 : BoxMajorant Geometry.b3618 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3618.Widths)
  · have he : Geometry.b3618.half 2 false=Geometry.b3985 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3985
  · have he : Geometry.b3618.half 2 true=Geometry.b3986 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3986

theorem bound3617 : BoxMajorant Geometry.b3617 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3617 2 (by decide +kernel) x hx hd ho).elim

theorem bound3348 : BoxMajorant Geometry.b3348 := by
  exact PositiveLeaves.L1635.bound

theorem bound3347 : BoxMajorant Geometry.b3347 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3347.Widths)
  · have he : Geometry.b3347.half 1 false=Geometry.b3621 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3621
  · have he : Geometry.b3347.half 1 true=Geometry.b3622 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3622

theorem bound3346 : BoxMajorant Geometry.b3346 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3346.Widths)
  · have he : Geometry.b3346.half 1 false=Geometry.b3619 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3619
  · have he : Geometry.b3346.half 1 true=Geometry.b3620 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3620

theorem bound3345 : BoxMajorant Geometry.b3345 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3345.Widths)
  · have he : Geometry.b3345.half 1 false=Geometry.b3617 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3617
  · have he : Geometry.b3345.half 1 true=Geometry.b3618 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3618

theorem bound3006 : BoxMajorant Geometry.b3006 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3006.Widths)
  · have he : Geometry.b3006.half 0 false=Geometry.b3347 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3347
  · have he : Geometry.b3006.half 0 true=Geometry.b3348 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3348

theorem bound3005 : BoxMajorant Geometry.b3005 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3005.Widths)
  · have he : Geometry.b3005.half 0 false=Geometry.b3345 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3345
  · have he : Geometry.b3005.half 0 true=Geometry.b3346 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3346

theorem bound2617 : BoxMajorant Geometry.b2617 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2617.Widths)
  · have he : Geometry.b2617.half 2 false=Geometry.b3005 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3005
  · have he : Geometry.b2617.half 2 true=Geometry.b3006 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3006

end N7.Kernel.Cover
