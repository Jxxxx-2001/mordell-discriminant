import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverProofs.P0372
import N7.Kernel.CoverProofs.P0373
import N7.Kernel.CoverProofs.P0374
import N7.Kernel.CoverProofs.P0375
import N7.Kernel.CoverProofs.P0376
import N7.Kernel.CoverProofs.P0377
import N7.Kernel.CoverProofs.P0378
import N7.Kernel.CoverProofs.P0379
import N7.Kernel.PositiveGroups.G0339
import N7.Kernel.PositiveGroups.G0340
import N7.Kernel.PositiveGroups.G0371
import N7.Kernel.PositiveGroups.G0400
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4932 : BoxMajorant Geometry.b4932 := by
  exact PositiveLeaves.L1729.bound

theorem bound4931 : BoxMajorant Geometry.b4931 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4931 2 (by decide +kernel) x hx hd ho).elim

theorem bound4930 : BoxMajorant Geometry.b4930 := by
  exact PositiveLeaves.L1731.bound

theorem bound4929 : BoxMajorant Geometry.b4929 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4929 2 (by decide +kernel) x hx hd ho).elim

theorem bound4927 : BoxMajorant Geometry.b4927 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4927 2 (by decide +kernel) x hx hd ho).elim

theorem bound4598 : BoxMajorant Geometry.b4598 := by
  exact PositiveLeaves.L1703.bound

theorem bound4590 : BoxMajorant Geometry.b4590 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4590.Widths)
  · have he : Geometry.b4590.half 2 false=Geometry.b4931 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4931
  · have he : Geometry.b4590.half 2 true=Geometry.b4932 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4932

theorem bound4589 : BoxMajorant Geometry.b4589 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4589.Widths)
  · have he : Geometry.b4589.half 2 false=Geometry.b4929 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4929
  · have he : Geometry.b4589.half 2 true=Geometry.b4930 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4930

theorem bound4588 : BoxMajorant Geometry.b4588 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4588.Widths)
  · have he : Geometry.b4588.half 2 false=Geometry.b4927 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4927
  · have he : Geometry.b4588.half 2 true=Geometry.b4928 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4928

theorem bound4587 : BoxMajorant Geometry.b4587 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4587 2 (by decide +kernel) x hx hd ho).elim

theorem bound4330 : BoxMajorant Geometry.b4330 := by
  exact PositiveLeaves.L1702.bound

theorem bound4329 : BoxMajorant Geometry.b4329 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4329.Widths)
  · have he : Geometry.b4329.half 1 false=Geometry.b4597 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4597
  · have he : Geometry.b4329.half 1 true=Geometry.b4598 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4598

theorem bound4328 : BoxMajorant Geometry.b4328 := by
  exact PositiveLeaves.L1708.bound

theorem bound4327 : BoxMajorant Geometry.b4327 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4327.Widths)
  · have he : Geometry.b4327.half 1 false=Geometry.b4595 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4595
  · have he : Geometry.b4327.half 1 true=Geometry.b4596 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4596

theorem bound4326 : BoxMajorant Geometry.b4326 := by
  exact PositiveLeaves.L1714.bound

theorem bound4325 : BoxMajorant Geometry.b4325 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4325.Widths)
  · have he : Geometry.b4325.half 1 false=Geometry.b4593 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4593
  · have he : Geometry.b4325.half 1 true=Geometry.b4594 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4594

theorem bound4324 : BoxMajorant Geometry.b4324 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4324.Widths)
  · have he : Geometry.b4324.half 1 false=Geometry.b4591 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4591
  · have he : Geometry.b4324.half 1 true=Geometry.b4592 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4592

theorem bound4323 : BoxMajorant Geometry.b4323 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4323 2 (by decide +kernel) x hx hd ho).elim

theorem bound4322 : BoxMajorant Geometry.b4322 := by
  exact PositiveLeaves.L1728.bound

theorem bound4321 : BoxMajorant Geometry.b4321 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4321.Widths)
  · have he : Geometry.b4321.half 1 false=Geometry.b4589 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4589
  · have he : Geometry.b4321.half 1 true=Geometry.b4590 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4590

theorem bound4320 : BoxMajorant Geometry.b4320 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4320.Widths)
  · have he : Geometry.b4320.half 1 false=Geometry.b4587 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4587
  · have he : Geometry.b4320.half 1 true=Geometry.b4588 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4588

theorem bound4319 : BoxMajorant Geometry.b4319 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4319 2 (by decide +kernel) x hx hd ho).elim

theorem bound3972 : BoxMajorant Geometry.b3972 := by
  exact PositiveLeaves.L1701.bound

theorem bound3971 : BoxMajorant Geometry.b3971 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3971.Widths)
  · have he : Geometry.b3971.half 0 false=Geometry.b4329 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4329
  · have he : Geometry.b3971.half 0 true=Geometry.b4330 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4330

theorem bound3970 : BoxMajorant Geometry.b3970 := by
  exact PositiveLeaves.L1707.bound

theorem bound3969 : BoxMajorant Geometry.b3969 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3969.Widths)
  · have he : Geometry.b3969.half 0 false=Geometry.b4327 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4327
  · have he : Geometry.b3969.half 0 true=Geometry.b4328 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4328

theorem bound3968 : BoxMajorant Geometry.b3968 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3968.Widths)
  · have he : Geometry.b3968.half 0 false=Geometry.b4325 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4325
  · have he : Geometry.b3968.half 0 true=Geometry.b4326 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4326

theorem bound3967 : BoxMajorant Geometry.b3967 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3967.Widths)
  · have he : Geometry.b3967.half 0 false=Geometry.b4323 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4323
  · have he : Geometry.b3967.half 0 true=Geometry.b4324 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4324

theorem bound3966 : BoxMajorant Geometry.b3966 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3966.Widths)
  · have he : Geometry.b3966.half 0 false=Geometry.b4321 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4321
  · have he : Geometry.b3966.half 0 true=Geometry.b4322 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4322

theorem bound3965 : BoxMajorant Geometry.b3965 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3965.Widths)
  · have he : Geometry.b3965.half 0 false=Geometry.b4319 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4319
  · have he : Geometry.b3965.half 0 true=Geometry.b4320 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4320

theorem bound3608 : BoxMajorant Geometry.b3608 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3608.Widths)
  · have he : Geometry.b3608.half 2 false=Geometry.b3971 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3971
  · have he : Geometry.b3608.half 2 true=Geometry.b3972 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3972

theorem bound3607 : BoxMajorant Geometry.b3607 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3607.Widths)
  · have he : Geometry.b3607.half 2 false=Geometry.b3969 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3969
  · have he : Geometry.b3607.half 2 true=Geometry.b3970 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3970

theorem bound3606 : BoxMajorant Geometry.b3606 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3606.Widths)
  · have he : Geometry.b3606.half 2 false=Geometry.b3967 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3967
  · have he : Geometry.b3606.half 2 true=Geometry.b3968 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3968

theorem bound3605 : BoxMajorant Geometry.b3605 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3605.Widths)
  · have he : Geometry.b3605.half 2 false=Geometry.b3965 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3965
  · have he : Geometry.b3605.half 2 true=Geometry.b3966 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3966

theorem bound3336 : BoxMajorant Geometry.b3336 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3336.Widths)
  · have he : Geometry.b3336.half 1 false=Geometry.b3607 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3607
  · have he : Geometry.b3336.half 1 true=Geometry.b3608 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3608

theorem bound3335 : BoxMajorant Geometry.b3335 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3335.Widths)
  · have he : Geometry.b3335.half 1 false=Geometry.b3605 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3605
  · have he : Geometry.b3335.half 1 true=Geometry.b3606 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3606

theorem bound2998 : BoxMajorant Geometry.b2998 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2998.Widths)
  · have he : Geometry.b2998.half 0 false=Geometry.b3335 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3335
  · have he : Geometry.b2998.half 0 true=Geometry.b3336 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3336

end N7.Kernel.Cover
