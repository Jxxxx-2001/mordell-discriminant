import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverProofs.P0336
import N7.Kernel.CoverProofs.P0337
import N7.Kernel.CoverProofs.P0338
import N7.Kernel.CoverProofs.P0339
import N7.Kernel.CoverProofs.P0340
import N7.Kernel.CoverProofs.P0341
import N7.Kernel.CoverProofs.P0342
import N7.Kernel.CoverProofs.P0343
import N7.Kernel.CoverProofs.P0344
import N7.Kernel.PositiveGroups.G0385
import N7.Kernel.PositiveGroups.G0409
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4746 : BoxMajorant Geometry.b4746 := by
  exact PositiveLeaves.L2814.bound

theorem bound4744 : BoxMajorant Geometry.b4744 := by
  exact PositiveLeaves.L2821.bound

theorem bound4741 : BoxMajorant Geometry.b4741 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4741 2 (by decide +kernel) x hx hd ho).elim

theorem bound4739 : BoxMajorant Geometry.b4739 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4739 2 (by decide +kernel) x hx hd ho).elim

theorem bound4737 : BoxMajorant Geometry.b4737 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4737 2 (by decide +kernel) x hx hd ho).elim

theorem bound4735 : BoxMajorant Geometry.b4735 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4735 2 (by decide +kernel) x hx hd ho).elim

theorem bound4733 : BoxMajorant Geometry.b4733 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4733 2 (by decide +kernel) x hx hd ho).elim

theorem bound4731 : BoxMajorant Geometry.b4731 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4731 2 (by decide +kernel) x hx hd ho).elim

theorem bound4729 : BoxMajorant Geometry.b4729 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4729 2 (by decide +kernel) x hx hd ho).elim

theorem bound4462 : BoxMajorant Geometry.b4462 := by
  exact PositiveLeaves.L2813.bound

theorem bound4461 : BoxMajorant Geometry.b4461 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4461.Widths)
  · have he : Geometry.b4461.half 2 false=Geometry.b4745 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4745
  · have he : Geometry.b4461.half 2 true=Geometry.b4746 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4746

theorem bound4460 : BoxMajorant Geometry.b4460 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4460.Widths)
  · have he : Geometry.b4460.half 2 false=Geometry.b4743 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4743
  · have he : Geometry.b4460.half 2 true=Geometry.b4744 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4744

theorem bound4459 : BoxMajorant Geometry.b4459 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4459.Widths)
  · have he : Geometry.b4459.half 2 false=Geometry.b4741 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4741
  · have he : Geometry.b4459.half 2 true=Geometry.b4742 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4742

theorem bound4458 : BoxMajorant Geometry.b4458 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4458.Widths)
  · have he : Geometry.b4458.half 2 false=Geometry.b4739 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4739
  · have he : Geometry.b4458.half 2 true=Geometry.b4740 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4740

theorem bound4457 : BoxMajorant Geometry.b4457 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4457.Widths)
  · have he : Geometry.b4457.half 2 false=Geometry.b4737 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4737
  · have he : Geometry.b4457.half 2 true=Geometry.b4738 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4738

theorem bound4456 : BoxMajorant Geometry.b4456 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4456.Widths)
  · have he : Geometry.b4456.half 2 false=Geometry.b4735 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4735
  · have he : Geometry.b4456.half 2 true=Geometry.b4736 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4736

theorem bound4455 : BoxMajorant Geometry.b4455 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4455 2 (by decide +kernel) x hx hd ho).elim

theorem bound4454 : BoxMajorant Geometry.b4454 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4454.Widths)
  · have he : Geometry.b4454.half 2 false=Geometry.b4733 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4733
  · have he : Geometry.b4454.half 2 true=Geometry.b4734 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4734

theorem bound4453 : BoxMajorant Geometry.b4453 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4453.Widths)
  · have he : Geometry.b4453.half 2 false=Geometry.b4731 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4731
  · have he : Geometry.b4453.half 2 true=Geometry.b4732 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4732

theorem bound4452 : BoxMajorant Geometry.b4452 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4452.Widths)
  · have he : Geometry.b4452.half 2 false=Geometry.b4729 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4729
  · have he : Geometry.b4452.half 2 true=Geometry.b4730 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4730

theorem bound4451 : BoxMajorant Geometry.b4451 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4451 2 (by decide +kernel) x hx hd ho).elim

theorem bound4162 : BoxMajorant Geometry.b4162 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4162.Widths)
  · have he : Geometry.b4162.half 1 false=Geometry.b4461 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4461
  · have he : Geometry.b4162.half 1 true=Geometry.b4462 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4462

theorem bound4161 : BoxMajorant Geometry.b4161 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4161.Widths)
  · have he : Geometry.b4161.half 1 false=Geometry.b4459 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4459
  · have he : Geometry.b4161.half 1 true=Geometry.b4460 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4460

theorem bound4160 : BoxMajorant Geometry.b4160 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4160.Widths)
  · have he : Geometry.b4160.half 1 false=Geometry.b4457 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4457
  · have he : Geometry.b4160.half 1 true=Geometry.b4458 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4458

theorem bound4159 : BoxMajorant Geometry.b4159 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4159.Widths)
  · have he : Geometry.b4159.half 1 false=Geometry.b4455 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4455
  · have he : Geometry.b4159.half 1 true=Geometry.b4456 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4456

theorem bound4158 : BoxMajorant Geometry.b4158 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4158.Widths)
  · have he : Geometry.b4158.half 1 false=Geometry.b4453 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4453
  · have he : Geometry.b4158.half 1 true=Geometry.b4454 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4454

theorem bound4157 : BoxMajorant Geometry.b4157 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4157.Widths)
  · have he : Geometry.b4157.half 1 false=Geometry.b4451 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4451
  · have he : Geometry.b4157.half 1 true=Geometry.b4452 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4452

theorem bound3742 : BoxMajorant Geometry.b3742 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3742.Widths)
  · have he : Geometry.b3742.half 0 false=Geometry.b4161 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4161
  · have he : Geometry.b3742.half 0 true=Geometry.b4162 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4162

theorem bound3741 : BoxMajorant Geometry.b3741 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3741 2 (by decide +kernel) x hx hd ho).elim

theorem bound3740 : BoxMajorant Geometry.b3740 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3740.Widths)
  · have he : Geometry.b3740.half 0 false=Geometry.b4159 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4159
  · have he : Geometry.b3740.half 0 true=Geometry.b4160 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4160

theorem bound3739 : BoxMajorant Geometry.b3739 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3739 2 (by decide +kernel) x hx hd ho).elim

theorem bound3738 : BoxMajorant Geometry.b3738 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3738.Widths)
  · have he : Geometry.b3738.half 0 false=Geometry.b4157 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4157
  · have he : Geometry.b3738.half 0 true=Geometry.b4158 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4158

theorem bound3737 : BoxMajorant Geometry.b3737 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3737 2 (by decide +kernel) x hx hd ho).elim

theorem bound3462 : BoxMajorant Geometry.b3462 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3462.Widths)
  · have he : Geometry.b3462.half 2 false=Geometry.b3741 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3741
  · have he : Geometry.b3462.half 2 true=Geometry.b3742 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3742

theorem bound3461 : BoxMajorant Geometry.b3461 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3461.Widths)
  · have he : Geometry.b3461.half 2 false=Geometry.b3739 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3739
  · have he : Geometry.b3461.half 2 true=Geometry.b3740 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3740

theorem bound3460 : BoxMajorant Geometry.b3460 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3460.Widths)
  · have he : Geometry.b3460.half 2 false=Geometry.b3737 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3737
  · have he : Geometry.b3460.half 2 true=Geometry.b3738 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3738

theorem bound3459 : BoxMajorant Geometry.b3459 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3459 2 (by decide +kernel) x hx hd ho).elim

theorem bound3188 : BoxMajorant Geometry.b3188 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3188.Widths)
  · have he : Geometry.b3188.half 1 false=Geometry.b3461 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3461
  · have he : Geometry.b3188.half 1 true=Geometry.b3462 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3462

theorem bound3187 : BoxMajorant Geometry.b3187 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3187.Widths)
  · have he : Geometry.b3187.half 1 false=Geometry.b3459 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3459
  · have he : Geometry.b3187.half 1 true=Geometry.b3460 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3460

theorem bound2802 : BoxMajorant Geometry.b2802 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2802.Widths)
  · have he : Geometry.b2802.half 0 false=Geometry.b3187 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3187
  · have he : Geometry.b2802.half 0 true=Geometry.b3188 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3188

end N7.Kernel.Cover
