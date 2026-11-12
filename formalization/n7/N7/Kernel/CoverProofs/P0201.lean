import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverProofs.P0354
import N7.Kernel.CoverProofs.P0355
import N7.Kernel.CoverProofs.P0356
import N7.Kernel.CoverProofs.P0357
import N7.Kernel.CoverProofs.P0358
import N7.Kernel.CoverProofs.P0359
import N7.Kernel.PositiveGroups.G0297
import N7.Kernel.PositiveGroups.G0321
import N7.Kernel.PositiveGroups.G0352
import N7.Kernel.PositiveGroups.G0383
import N7.Kernel.PositiveGroups.G0406
import N7.Kernel.PositiveGroups.G0407
import N7.Kernel.PositiveGroups.G0424
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4800 : BoxMajorant Geometry.b4800 := by
  exact PositiveLeaves.L2597.bound

theorem bound4799 : BoxMajorant Geometry.b4799 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4799 2 (by decide +kernel) x hx hd ho).elim

theorem bound4798 : BoxMajorant Geometry.b4798 := by
  exact PositiveLeaves.L2599.bound

theorem bound4797 : BoxMajorant Geometry.b4797 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4797 2 (by decide +kernel) x hx hd ho).elim

theorem bound4796 : BoxMajorant Geometry.b4796 := by
  exact PositiveLeaves.L2603.bound

theorem bound4794 : BoxMajorant Geometry.b4794 := by
  exact PositiveLeaves.L2608.bound

theorem bound4789 : BoxMajorant Geometry.b4789 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4789 2 (by decide +kernel) x hx hd ho).elim

theorem bound4509 : BoxMajorant Geometry.b4509 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4509 0 (by decide +kernel) x hx hd ho).elim

theorem bound4508 : BoxMajorant Geometry.b4508 := by
  exact PositiveLeaves.L2596.bound

theorem bound4507 : BoxMajorant Geometry.b4507 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4507.Widths)
  · have he : Geometry.b4507.half 2 false=Geometry.b4799 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4799
  · have he : Geometry.b4507.half 2 true=Geometry.b4800 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4800

theorem bound4506 : BoxMajorant Geometry.b4506 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4506.Widths)
  · have he : Geometry.b4506.half 2 false=Geometry.b4797 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4797
  · have he : Geometry.b4506.half 2 true=Geometry.b4798 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4798

theorem bound4505 : BoxMajorant Geometry.b4505 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4505 2 (by decide +kernel) x hx hd ho).elim

theorem bound4504 : BoxMajorant Geometry.b4504 := by
  exact PositiveLeaves.L2602.bound

theorem bound4503 : BoxMajorant Geometry.b4503 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4503.Widths)
  · have he : Geometry.b4503.half 2 false=Geometry.b4795 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4795
  · have he : Geometry.b4503.half 2 true=Geometry.b4796 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4796

theorem bound4502 : BoxMajorant Geometry.b4502 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4502.Widths)
  · have he : Geometry.b4502.half 2 false=Geometry.b4793 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4793
  · have he : Geometry.b4502.half 2 true=Geometry.b4794 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4794

theorem bound4501 : BoxMajorant Geometry.b4501 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4501.Widths)
  · have he : Geometry.b4501.half 2 false=Geometry.b4791 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4791
  · have he : Geometry.b4501.half 2 true=Geometry.b4792 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4792

theorem bound4500 : BoxMajorant Geometry.b4500 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4500.Widths)
  · have he : Geometry.b4500.half 2 false=Geometry.b4789 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4789
  · have he : Geometry.b4500.half 2 true=Geometry.b4790 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4790

theorem bound4499 : BoxMajorant Geometry.b4499 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4499 2 (by decide +kernel) x hx hd ho).elim

theorem bound4204 : BoxMajorant Geometry.b4204 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4204 0 (by decide +kernel) x hx hd ho).elim

theorem bound4203 : BoxMajorant Geometry.b4203 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4203.Widths)
  · have he : Geometry.b4203.half 1 false=Geometry.b4509 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4509
  · have he : Geometry.b4203.half 1 true=Geometry.b4510 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4510

theorem bound4202 : BoxMajorant Geometry.b4202 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4202.Widths)
  · have he : Geometry.b4202.half 1 false=Geometry.b4507 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4507
  · have he : Geometry.b4202.half 1 true=Geometry.b4508 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4508

theorem bound4201 : BoxMajorant Geometry.b4201 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4201.Widths)
  · have he : Geometry.b4201.half 1 false=Geometry.b4505 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4505
  · have he : Geometry.b4201.half 1 true=Geometry.b4506 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4506

theorem bound4200 : BoxMajorant Geometry.b4200 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4200.Widths)
  · have he : Geometry.b4200.half 1 false=Geometry.b4503 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4503
  · have he : Geometry.b4200.half 1 true=Geometry.b4504 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4504

theorem bound4199 : BoxMajorant Geometry.b4199 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4199.Widths)
  · have he : Geometry.b4199.half 1 false=Geometry.b4501 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4501
  · have he : Geometry.b4199.half 1 true=Geometry.b4502 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4502

theorem bound4198 : BoxMajorant Geometry.b4198 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4198.Widths)
  · have he : Geometry.b4198.half 1 false=Geometry.b4499 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4499
  · have he : Geometry.b4198.half 1 true=Geometry.b4500 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4500

theorem bound4197 : BoxMajorant Geometry.b4197 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4197 2 (by decide +kernel) x hx hd ho).elim

theorem bound3796 : BoxMajorant Geometry.b3796 := by
  exact PositiveLeaves.L2590.bound

theorem bound3795 : BoxMajorant Geometry.b3795 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3795.Widths)
  · have he : Geometry.b3795.half 0 false=Geometry.b4203 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4203
  · have he : Geometry.b3795.half 0 true=Geometry.b4204 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4204

theorem bound3794 : BoxMajorant Geometry.b3794 := by
  exact PositiveLeaves.L2595.bound

theorem bound3793 : BoxMajorant Geometry.b3793 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3793.Widths)
  · have he : Geometry.b3793.half 0 false=Geometry.b4201 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4201
  · have he : Geometry.b3793.half 0 true=Geometry.b4202 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4202

theorem bound3792 : BoxMajorant Geometry.b3792 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3792.Widths)
  · have he : Geometry.b3792.half 0 false=Geometry.b4199 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4199
  · have he : Geometry.b3792.half 0 true=Geometry.b4200 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4200

theorem bound3791 : BoxMajorant Geometry.b3791 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3791.Widths)
  · have he : Geometry.b3791.half 0 false=Geometry.b4197 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4197
  · have he : Geometry.b3791.half 0 true=Geometry.b4198 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4198

theorem bound3498 : BoxMajorant Geometry.b3498 := by
  exact PositiveLeaves.L2589.bound

theorem bound3497 : BoxMajorant Geometry.b3497 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3497.Widths)
  · have he : Geometry.b3497.half 2 false=Geometry.b3795 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3795
  · have he : Geometry.b3497.half 2 true=Geometry.b3796 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3796

theorem bound3496 : BoxMajorant Geometry.b3496 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3496.Widths)
  · have he : Geometry.b3496.half 2 false=Geometry.b3793 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3793
  · have he : Geometry.b3496.half 2 true=Geometry.b3794 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3794

theorem bound3495 : BoxMajorant Geometry.b3495 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3495.Widths)
  · have he : Geometry.b3495.half 2 false=Geometry.b3791 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3791
  · have he : Geometry.b3495.half 2 true=Geometry.b3792 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3792

theorem bound3212 : BoxMajorant Geometry.b3212 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3212.Widths)
  · have he : Geometry.b3212.half 1 false=Geometry.b3497 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3497
  · have he : Geometry.b3212.half 1 true=Geometry.b3498 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3498

theorem bound3211 : BoxMajorant Geometry.b3211 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3211.Widths)
  · have he : Geometry.b3211.half 1 false=Geometry.b3495 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3495
  · have he : Geometry.b3211.half 1 true=Geometry.b3496 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3496

theorem bound2834 : BoxMajorant Geometry.b2834 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2834.Widths)
  · have he : Geometry.b2834.half 0 false=Geometry.b3211 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3211
  · have he : Geometry.b2834.half 0 true=Geometry.b3212 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3212

end N7.Kernel.Cover
