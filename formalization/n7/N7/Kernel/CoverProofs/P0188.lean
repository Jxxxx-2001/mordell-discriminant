import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverProofs.P0345
import N7.Kernel.CoverProofs.P0346
import N7.Kernel.CoverProofs.P0347
import N7.Kernel.CoverProofs.P0348
import N7.Kernel.CoverProofs.P0349
import N7.Kernel.CoverProofs.P0350
import N7.Kernel.CoverProofs.P0351
import N7.Kernel.CoverProofs.P0352
import N7.Kernel.CoverProofs.P0353
import N7.Kernel.PositiveGroups.G0323
import N7.Kernel.PositiveGroups.G0353
import N7.Kernel.PositiveGroups.G0384
import N7.Kernel.PositiveGroups.G0385
import N7.Kernel.PositiveGroups.G0407
import N7.Kernel.PositiveGroups.G0408
import N7.Kernel.PositiveGroups.G0425
import N7.Kernel.PositiveGroups.G0426
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4754 : BoxMajorant Geometry.b4754 := by
  exact PositiveLeaves.L2791.bound

theorem bound4752 : BoxMajorant Geometry.b4752 := by
  exact PositiveLeaves.L2796.bound

theorem bound4750 : BoxMajorant Geometry.b4750 := by
  exact PositiveLeaves.L2801.bound

theorem bound4749 : BoxMajorant Geometry.b4749 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4749 2 (by decide +kernel) x hx hd ho).elim

theorem bound4747 : BoxMajorant Geometry.b4747 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4747 2 (by decide +kernel) x hx hd ho).elim

theorem bound4478 : BoxMajorant Geometry.b4478 := by
  exact PositiveLeaves.L2765.bound

theorem bound4476 : BoxMajorant Geometry.b4476 := by
  exact PositiveLeaves.L2769.bound

theorem bound4474 : BoxMajorant Geometry.b4474 := by
  exact PositiveLeaves.L2775.bound

theorem bound4471 : BoxMajorant Geometry.b4471 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4471 2 (by decide +kernel) x hx hd ho).elim

theorem bound4470 : BoxMajorant Geometry.b4470 := by
  exact PositiveLeaves.L2783.bound

theorem bound4467 : BoxMajorant Geometry.b4467 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4467 2 (by decide +kernel) x hx hd ho).elim

theorem bound4466 : BoxMajorant Geometry.b4466 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4466.Widths)
  · have he : Geometry.b4466.half 2 false=Geometry.b4753 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4753
  · have he : Geometry.b4466.half 2 true=Geometry.b4754 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4754

theorem bound4465 : BoxMajorant Geometry.b4465 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4465.Widths)
  · have he : Geometry.b4465.half 2 false=Geometry.b4751 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4751
  · have he : Geometry.b4465.half 2 true=Geometry.b4752 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4752

theorem bound4464 : BoxMajorant Geometry.b4464 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4464.Widths)
  · have he : Geometry.b4464.half 2 false=Geometry.b4749 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4749
  · have he : Geometry.b4464.half 2 true=Geometry.b4750 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4750

theorem bound4463 : BoxMajorant Geometry.b4463 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4463.Widths)
  · have he : Geometry.b4463.half 2 false=Geometry.b4747 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4747
  · have he : Geometry.b4463.half 2 true=Geometry.b4748 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4748

theorem bound4174 : BoxMajorant Geometry.b4174 := by
  exact PositiveLeaves.L2764.bound

theorem bound4173 : BoxMajorant Geometry.b4173 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4173.Widths)
  · have he : Geometry.b4173.half 1 false=Geometry.b4477 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4477
  · have he : Geometry.b4173.half 1 true=Geometry.b4478 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4478

theorem bound4172 : BoxMajorant Geometry.b4172 := by
  exact PositiveLeaves.L2768.bound

theorem bound4171 : BoxMajorant Geometry.b4171 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4171.Widths)
  · have he : Geometry.b4171.half 1 false=Geometry.b4475 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4475
  · have he : Geometry.b4171.half 1 true=Geometry.b4476 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4476

theorem bound4170 : BoxMajorant Geometry.b4170 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4170.Widths)
  · have he : Geometry.b4170.half 1 false=Geometry.b4473 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4473
  · have he : Geometry.b4170.half 1 true=Geometry.b4474 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4474

theorem bound4169 : BoxMajorant Geometry.b4169 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4169.Widths)
  · have he : Geometry.b4169.half 1 false=Geometry.b4471 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4471
  · have he : Geometry.b4169.half 1 true=Geometry.b4472 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4472

theorem bound4168 : BoxMajorant Geometry.b4168 := by
  exact PositiveLeaves.L2782.bound

theorem bound4167 : BoxMajorant Geometry.b4167 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4167.Widths)
  · have he : Geometry.b4167.half 1 false=Geometry.b4469 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4469
  · have he : Geometry.b4167.half 1 true=Geometry.b4470 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4470

theorem bound4166 : BoxMajorant Geometry.b4166 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4166.Widths)
  · have he : Geometry.b4166.half 1 false=Geometry.b4467 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4467
  · have he : Geometry.b4166.half 1 true=Geometry.b4468 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4468

theorem bound4165 : BoxMajorant Geometry.b4165 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4165 2 (by decide +kernel) x hx hd ho).elim

theorem bound4164 : BoxMajorant Geometry.b4164 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4164.Widths)
  · have he : Geometry.b4164.half 1 false=Geometry.b4465 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4465
  · have he : Geometry.b4164.half 1 true=Geometry.b4466 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4466

theorem bound4163 : BoxMajorant Geometry.b4163 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4163.Widths)
  · have he : Geometry.b4163.half 1 false=Geometry.b4463 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4463
  · have he : Geometry.b4163.half 1 true=Geometry.b4464 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4464

theorem bound3750 : BoxMajorant Geometry.b3750 := by
  exact PositiveLeaves.L2763.bound

theorem bound3749 : BoxMajorant Geometry.b3749 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3749.Widths)
  · have he : Geometry.b3749.half 0 false=Geometry.b4173 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4173
  · have he : Geometry.b3749.half 0 true=Geometry.b4174 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4174

theorem bound3748 : BoxMajorant Geometry.b3748 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3748.Widths)
  · have he : Geometry.b3748.half 0 false=Geometry.b4171 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4171
  · have he : Geometry.b3748.half 0 true=Geometry.b4172 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4172

theorem bound3747 : BoxMajorant Geometry.b3747 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3747.Widths)
  · have he : Geometry.b3747.half 0 false=Geometry.b4169 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4169
  · have he : Geometry.b3747.half 0 true=Geometry.b4170 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4170

theorem bound3746 : BoxMajorant Geometry.b3746 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3746.Widths)
  · have he : Geometry.b3746.half 0 false=Geometry.b4167 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4167
  · have he : Geometry.b3746.half 0 true=Geometry.b4168 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4168

theorem bound3745 : BoxMajorant Geometry.b3745 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3745.Widths)
  · have he : Geometry.b3745.half 0 false=Geometry.b4165 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4165
  · have he : Geometry.b3745.half 0 true=Geometry.b4166 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4166

theorem bound3744 : BoxMajorant Geometry.b3744 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3744.Widths)
  · have he : Geometry.b3744.half 0 false=Geometry.b4163 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4163
  · have he : Geometry.b3744.half 0 true=Geometry.b4164 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4164

theorem bound3743 : BoxMajorant Geometry.b3743 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3743 2 (by decide +kernel) x hx hd ho).elim

theorem bound3466 : BoxMajorant Geometry.b3466 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3466.Widths)
  · have he : Geometry.b3466.half 2 false=Geometry.b3749 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3749
  · have he : Geometry.b3466.half 2 true=Geometry.b3750 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3750

theorem bound3465 : BoxMajorant Geometry.b3465 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3465.Widths)
  · have he : Geometry.b3465.half 2 false=Geometry.b3747 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3747
  · have he : Geometry.b3465.half 2 true=Geometry.b3748 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3748

theorem bound3464 : BoxMajorant Geometry.b3464 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3464.Widths)
  · have he : Geometry.b3464.half 2 false=Geometry.b3745 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3745
  · have he : Geometry.b3464.half 2 true=Geometry.b3746 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3746

theorem bound3463 : BoxMajorant Geometry.b3463 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3463.Widths)
  · have he : Geometry.b3463.half 2 false=Geometry.b3743 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3743
  · have he : Geometry.b3463.half 2 true=Geometry.b3744 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3744

theorem bound3190 : BoxMajorant Geometry.b3190 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3190.Widths)
  · have he : Geometry.b3190.half 1 false=Geometry.b3465 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3465
  · have he : Geometry.b3190.half 1 true=Geometry.b3466 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3466

theorem bound3189 : BoxMajorant Geometry.b3189 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3189.Widths)
  · have he : Geometry.b3189.half 1 false=Geometry.b3463 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3463
  · have he : Geometry.b3189.half 1 true=Geometry.b3464 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3464

theorem bound2804 : BoxMajorant Geometry.b2804 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2804.Widths)
  · have he : Geometry.b2804.half 0 false=Geometry.b3189 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3189
  · have he : Geometry.b2804.half 0 true=Geometry.b3190 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3190

end N7.Kernel.Cover
