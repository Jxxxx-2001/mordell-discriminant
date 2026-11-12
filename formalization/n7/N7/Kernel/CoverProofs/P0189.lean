import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.PositiveGroups.G0322
import N7.Kernel.PositiveGroups.G0323
import N7.Kernel.PositiveGroups.G0353
import N7.Kernel.PositiveGroups.G0383
import N7.Kernel.PositiveGroups.G0384
import N7.Kernel.PositiveGroups.G0407
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5142 : BoxMajorant Geometry.b5142 := by
  exact PositiveLeaves.L2755.bound

theorem bound5141 : BoxMajorant Geometry.b5141 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5141 2 (by decide +kernel) x hx hd ho).elim

theorem bound4774 : BoxMajorant Geometry.b4774 := by
  exact PositiveLeaves.L2745.bound

theorem bound4773 : BoxMajorant Geometry.b4773 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4773 2 (by decide +kernel) x hx hd ho).elim

theorem bound4772 : BoxMajorant Geometry.b4772 := by
  exact PositiveLeaves.L2747.bound

theorem bound4771 : BoxMajorant Geometry.b4771 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4771 2 (by decide +kernel) x hx hd ho).elim

theorem bound4770 : BoxMajorant Geometry.b4770 := by
  exact PositiveLeaves.L2751.bound

theorem bound4769 : BoxMajorant Geometry.b4769 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4769 2 (by decide +kernel) x hx hd ho).elim

theorem bound4768 : BoxMajorant Geometry.b4768 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4768.Widths)
  · have he : Geometry.b4768.half 0 false=Geometry.b5141 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5141
  · have he : Geometry.b4768.half 0 true=Geometry.b5142 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5142

theorem bound4767 : BoxMajorant Geometry.b4767 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4767 2 (by decide +kernel) x hx hd ho).elim

theorem bound4484 : BoxMajorant Geometry.b4484 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4484.Widths)
  · have he : Geometry.b4484.half 2 false=Geometry.b4773 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4773
  · have he : Geometry.b4484.half 2 true=Geometry.b4774 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4774

theorem bound4483 : BoxMajorant Geometry.b4483 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4483.Widths)
  · have he : Geometry.b4483.half 2 false=Geometry.b4771 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4771
  · have he : Geometry.b4483.half 2 true=Geometry.b4772 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4772

theorem bound4482 : BoxMajorant Geometry.b4482 := by
  exact PositiveLeaves.L2750.bound

theorem bound4481 : BoxMajorant Geometry.b4481 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4481.Widths)
  · have he : Geometry.b4481.half 2 false=Geometry.b4769 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4769
  · have he : Geometry.b4481.half 2 true=Geometry.b4770 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4770

theorem bound4480 : BoxMajorant Geometry.b4480 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4480.Widths)
  · have he : Geometry.b4480.half 2 false=Geometry.b4767 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4767
  · have he : Geometry.b4480.half 2 true=Geometry.b4768 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4768

theorem bound4479 : BoxMajorant Geometry.b4479 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4479 2 (by decide +kernel) x hx hd ho).elim

theorem bound4182 : BoxMajorant Geometry.b4182 := by
  exact PositiveLeaves.L2742.bound

theorem bound4181 : BoxMajorant Geometry.b4181 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4181 2 (by decide +kernel) x hx hd ho).elim

theorem bound4180 : BoxMajorant Geometry.b4180 := by
  exact PositiveLeaves.L2744.bound

theorem bound4179 : BoxMajorant Geometry.b4179 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4179.Widths)
  · have he : Geometry.b4179.half 1 false=Geometry.b4483 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4483
  · have he : Geometry.b4179.half 1 true=Geometry.b4484 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4484

theorem bound4178 : BoxMajorant Geometry.b4178 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4178.Widths)
  · have he : Geometry.b4178.half 1 false=Geometry.b4481 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4481
  · have he : Geometry.b4178.half 1 true=Geometry.b4482 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4482

theorem bound4177 : BoxMajorant Geometry.b4177 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4177 2 (by decide +kernel) x hx hd ho).elim

theorem bound4176 : BoxMajorant Geometry.b4176 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4176.Widths)
  · have he : Geometry.b4176.half 1 false=Geometry.b4479 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4479
  · have he : Geometry.b4176.half 1 true=Geometry.b4480 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4480

theorem bound4175 : BoxMajorant Geometry.b4175 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4175 2 (by decide +kernel) x hx hd ho).elim

theorem bound3758 : BoxMajorant Geometry.b3758 := by
  exact PositiveLeaves.L2741.bound

theorem bound3757 : BoxMajorant Geometry.b3757 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3757.Widths)
  · have he : Geometry.b3757.half 0 false=Geometry.b4181 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4181
  · have he : Geometry.b3757.half 0 true=Geometry.b4182 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4182

theorem bound3756 : BoxMajorant Geometry.b3756 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3756.Widths)
  · have he : Geometry.b3756.half 0 false=Geometry.b4179 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4179
  · have he : Geometry.b3756.half 0 true=Geometry.b4180 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4180

theorem bound3755 : BoxMajorant Geometry.b3755 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3755 2 (by decide +kernel) x hx hd ho).elim

theorem bound3754 : BoxMajorant Geometry.b3754 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3754.Widths)
  · have he : Geometry.b3754.half 0 false=Geometry.b4177 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4177
  · have he : Geometry.b3754.half 0 true=Geometry.b4178 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4178

theorem bound3753 : BoxMajorant Geometry.b3753 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3753 2 (by decide +kernel) x hx hd ho).elim

theorem bound3752 : BoxMajorant Geometry.b3752 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3752.Widths)
  · have he : Geometry.b3752.half 0 false=Geometry.b4175 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4175
  · have he : Geometry.b3752.half 0 true=Geometry.b4176 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4176

theorem bound3751 : BoxMajorant Geometry.b3751 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3751 2 (by decide +kernel) x hx hd ho).elim

theorem bound3470 : BoxMajorant Geometry.b3470 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3470.Widths)
  · have he : Geometry.b3470.half 2 false=Geometry.b3757 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3757
  · have he : Geometry.b3470.half 2 true=Geometry.b3758 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3758

theorem bound3469 : BoxMajorant Geometry.b3469 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3469.Widths)
  · have he : Geometry.b3469.half 2 false=Geometry.b3755 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3755
  · have he : Geometry.b3469.half 2 true=Geometry.b3756 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3756

theorem bound3468 : BoxMajorant Geometry.b3468 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3468.Widths)
  · have he : Geometry.b3468.half 2 false=Geometry.b3753 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3753
  · have he : Geometry.b3468.half 2 true=Geometry.b3754 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3754

theorem bound3467 : BoxMajorant Geometry.b3467 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3467.Widths)
  · have he : Geometry.b3467.half 2 false=Geometry.b3751 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3751
  · have he : Geometry.b3467.half 2 true=Geometry.b3752 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3752

theorem bound3192 : BoxMajorant Geometry.b3192 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3192.Widths)
  · have he : Geometry.b3192.half 1 false=Geometry.b3469 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3469
  · have he : Geometry.b3192.half 1 true=Geometry.b3470 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3470

theorem bound3191 : BoxMajorant Geometry.b3191 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3191.Widths)
  · have he : Geometry.b3191.half 1 false=Geometry.b3467 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3467
  · have he : Geometry.b3191.half 1 true=Geometry.b3468 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3468

theorem bound2806 : BoxMajorant Geometry.b2806 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2806.Widths)
  · have he : Geometry.b2806.half 0 false=Geometry.b3191 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3191
  · have he : Geometry.b2806.half 0 true=Geometry.b3192 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3192

end N7.Kernel.Cover
