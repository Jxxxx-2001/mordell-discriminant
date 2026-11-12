import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.PositiveGroups.G0267
import N7.Kernel.PositiveGroups.G0268
import N7.Kernel.PositiveGroups.G0298
import N7.Kernel.PositiveGroups.G0321
import N7.Kernel.PositiveGroups.G0322
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4784 : BoxMajorant Geometry.b4784 := by
  exact PositiveLeaves.L2688.bound

theorem bound4783 : BoxMajorant Geometry.b4783 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4783 2 (by decide +kernel) x hx hd ho).elim

theorem bound4782 : BoxMajorant Geometry.b4782 := by
  exact PositiveLeaves.L2692.bound

theorem bound4781 : BoxMajorant Geometry.b4781 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4781 2 (by decide +kernel) x hx hd ho).elim

theorem bound4780 : BoxMajorant Geometry.b4780 := by
  exact PositiveLeaves.L2694.bound

theorem bound4779 : BoxMajorant Geometry.b4779 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4779 2 (by decide +kernel) x hx hd ho).elim

theorem bound4492 : BoxMajorant Geometry.b4492 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4492.Widths)
  · have he : Geometry.b4492.half 2 false=Geometry.b4783 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4783
  · have he : Geometry.b4492.half 2 true=Geometry.b4784 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4784

theorem bound4491 : BoxMajorant Geometry.b4491 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4491 2 (by decide +kernel) x hx hd ho).elim

theorem bound4490 : BoxMajorant Geometry.b4490 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4490.Widths)
  · have he : Geometry.b4490.half 2 false=Geometry.b4781 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4781
  · have he : Geometry.b4490.half 2 true=Geometry.b4782 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4782

theorem bound4489 : BoxMajorant Geometry.b4489 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4489.Widths)
  · have he : Geometry.b4489.half 2 false=Geometry.b4779 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4779
  · have he : Geometry.b4489.half 2 true=Geometry.b4780 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4780

theorem bound4190 : BoxMajorant Geometry.b4190 := by
  exact PositiveLeaves.L2687.bound

theorem bound4189 : BoxMajorant Geometry.b4189 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4189.Widths)
  · have he : Geometry.b4189.half 1 false=Geometry.b4491 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4491
  · have he : Geometry.b4189.half 1 true=Geometry.b4492 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4492

theorem bound4188 : BoxMajorant Geometry.b4188 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4188.Widths)
  · have he : Geometry.b4188.half 1 false=Geometry.b4489 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4489
  · have he : Geometry.b4188.half 1 true=Geometry.b4490 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4490

theorem bound4187 : BoxMajorant Geometry.b4187 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4187 2 (by decide +kernel) x hx hd ho).elim

theorem bound3780 : BoxMajorant Geometry.b3780 := by
  exact PositiveLeaves.L2686.bound

theorem bound3779 : BoxMajorant Geometry.b3779 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3779.Widths)
  · have he : Geometry.b3779.half 0 false=Geometry.b4189 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4189
  · have he : Geometry.b3779.half 0 true=Geometry.b4190 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4190

theorem bound3778 : BoxMajorant Geometry.b3778 := by
  exact PositiveLeaves.L2691.bound

theorem bound3777 : BoxMajorant Geometry.b3777 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3777.Widths)
  · have he : Geometry.b3777.half 0 false=Geometry.b4187 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4187
  · have he : Geometry.b3777.half 0 true=Geometry.b4188 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4188

theorem bound3776 : BoxMajorant Geometry.b3776 := by
  exact PositiveLeaves.L2697.bound

theorem bound3775 : BoxMajorant Geometry.b3775 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3775 2 (by decide +kernel) x hx hd ho).elim

theorem bound3774 : BoxMajorant Geometry.b3774 := by
  exact PositiveLeaves.L2699.bound

theorem bound3773 : BoxMajorant Geometry.b3773 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3773 2 (by decide +kernel) x hx hd ho).elim

theorem bound3484 : BoxMajorant Geometry.b3484 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3484.Widths)
  · have he : Geometry.b3484.half 2 false=Geometry.b3779 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3779
  · have he : Geometry.b3484.half 2 true=Geometry.b3780 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3780

theorem bound3483 : BoxMajorant Geometry.b3483 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3483.Widths)
  · have he : Geometry.b3483.half 2 false=Geometry.b3777 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3777
  · have he : Geometry.b3483.half 2 true=Geometry.b3778 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3778

theorem bound3482 : BoxMajorant Geometry.b3482 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3482.Widths)
  · have he : Geometry.b3482.half 2 false=Geometry.b3775 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3775
  · have he : Geometry.b3482.half 2 true=Geometry.b3776 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3776

theorem bound3481 : BoxMajorant Geometry.b3481 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3481.Widths)
  · have he : Geometry.b3481.half 2 false=Geometry.b3773 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3773
  · have he : Geometry.b3481.half 2 true=Geometry.b3774 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3774

theorem bound3202 : BoxMajorant Geometry.b3202 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3202.Widths)
  · have he : Geometry.b3202.half 1 false=Geometry.b3483 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3483
  · have he : Geometry.b3202.half 1 true=Geometry.b3484 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3484

theorem bound3201 : BoxMajorant Geometry.b3201 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3201.Widths)
  · have he : Geometry.b3201.half 1 false=Geometry.b3481 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3481
  · have he : Geometry.b3201.half 1 true=Geometry.b3482 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3482

theorem bound2823 : BoxMajorant Geometry.b2823 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2823.Widths)
  · have he : Geometry.b2823.half 0 false=Geometry.b3201 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3201
  · have he : Geometry.b2823.half 0 true=Geometry.b3202 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3202

end N7.Kernel.Cover
