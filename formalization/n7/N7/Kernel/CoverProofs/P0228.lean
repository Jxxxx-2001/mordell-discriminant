import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverProofs.P0365
import N7.Kernel.PositiveGroups.G0293
import N7.Kernel.PositiveGroups.G0317
import N7.Kernel.PositiveGroups.G0348
import N7.Kernel.PositiveGroups.G0380
import N7.Kernel.PositiveGroups.G0404
import N7.Kernel.PositiveGroups.G0422
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5164 : BoxMajorant Geometry.b5164 := by
  exact PositiveLeaves.L2081.bound

theorem bound5163 : BoxMajorant Geometry.b5163 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5163 2 (by decide +kernel) x hx hd ho).elim

theorem bound5162 : BoxMajorant Geometry.b5162 := by
  exact PositiveLeaves.L2084.bound

theorem bound5161 : BoxMajorant Geometry.b5161 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5161 2 (by decide +kernel) x hx hd ho).elim

theorem bound4828 : BoxMajorant Geometry.b4828 := by
  exact PositiveLeaves.L2069.bound

theorem bound4826 : BoxMajorant Geometry.b4826 := by
  exact PositiveLeaves.L2072.bound

theorem bound4825 : BoxMajorant Geometry.b4825 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4825 2 (by decide +kernel) x hx hd ho).elim

theorem bound4824 : BoxMajorant Geometry.b4824 := by
  exact PositiveLeaves.L2076.bound

theorem bound4823 : BoxMajorant Geometry.b4823 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4823 2 (by decide +kernel) x hx hd ho).elim

theorem bound4822 : BoxMajorant Geometry.b4822 := by
  exact PositiveLeaves.L2078.bound

theorem bound4821 : BoxMajorant Geometry.b4821 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4821 2 (by decide +kernel) x hx hd ho).elim

theorem bound4820 : BoxMajorant Geometry.b4820 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4820.Widths)
  · have he : Geometry.b4820.half 0 false=Geometry.b5163 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5163
  · have he : Geometry.b4820.half 0 true=Geometry.b5164 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5164

theorem bound4819 : BoxMajorant Geometry.b4819 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4819 2 (by decide +kernel) x hx hd ho).elim

theorem bound4818 : BoxMajorant Geometry.b4818 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4818.Widths)
  · have he : Geometry.b4818.half 0 false=Geometry.b5161 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5161
  · have he : Geometry.b4818.half 0 true=Geometry.b5162 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5162

theorem bound4817 : BoxMajorant Geometry.b4817 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4817 2 (by decide +kernel) x hx hd ho).elim

theorem bound4526 : BoxMajorant Geometry.b4526 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4526.Widths)
  · have he : Geometry.b4526.half 2 false=Geometry.b4827 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4827
  · have he : Geometry.b4526.half 2 true=Geometry.b4828 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4828

theorem bound4525 : BoxMajorant Geometry.b4525 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4525.Widths)
  · have he : Geometry.b4525.half 2 false=Geometry.b4825 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4825
  · have he : Geometry.b4525.half 2 true=Geometry.b4826 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4826

theorem bound4524 : BoxMajorant Geometry.b4524 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4524.Widths)
  · have he : Geometry.b4524.half 2 false=Geometry.b4823 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4823
  · have he : Geometry.b4524.half 2 true=Geometry.b4824 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4824

theorem bound4523 : BoxMajorant Geometry.b4523 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4523.Widths)
  · have he : Geometry.b4523.half 2 false=Geometry.b4821 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4821
  · have he : Geometry.b4523.half 2 true=Geometry.b4822 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4822

theorem bound4522 : BoxMajorant Geometry.b4522 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4522.Widths)
  · have he : Geometry.b4522.half 2 false=Geometry.b4819 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4819
  · have he : Geometry.b4522.half 2 true=Geometry.b4820 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4820

theorem bound4521 : BoxMajorant Geometry.b4521 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4521.Widths)
  · have he : Geometry.b4521.half 2 false=Geometry.b4817 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4817
  · have he : Geometry.b4521.half 2 true=Geometry.b4818 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4818

theorem bound4228 : BoxMajorant Geometry.b4228 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4228.Widths)
  · have he : Geometry.b4228.half 1 false=Geometry.b4525 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4525
  · have he : Geometry.b4228.half 1 true=Geometry.b4526 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4526

theorem bound4227 : BoxMajorant Geometry.b4227 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4227 2 (by decide +kernel) x hx hd ho).elim

theorem bound4226 : BoxMajorant Geometry.b4226 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4226.Widths)
  · have he : Geometry.b4226.half 1 false=Geometry.b4523 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4523
  · have he : Geometry.b4226.half 1 true=Geometry.b4524 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4524

theorem bound4225 : BoxMajorant Geometry.b4225 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4225 2 (by decide +kernel) x hx hd ho).elim

theorem bound4224 : BoxMajorant Geometry.b4224 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4224.Widths)
  · have he : Geometry.b4224.half 1 false=Geometry.b4521 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4521
  · have he : Geometry.b4224.half 1 true=Geometry.b4522 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4522

theorem bound4223 : BoxMajorant Geometry.b4223 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4223 2 (by decide +kernel) x hx hd ho).elim

theorem bound3856 : BoxMajorant Geometry.b3856 := by
  exact PositiveLeaves.L2068.bound

theorem bound3855 : BoxMajorant Geometry.b3855 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3855.Widths)
  · have he : Geometry.b3855.half 0 false=Geometry.b4227 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4227
  · have he : Geometry.b3855.half 0 true=Geometry.b4228 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4228

theorem bound3854 : BoxMajorant Geometry.b3854 := by
  exact PositiveLeaves.L2075.bound

theorem bound3853 : BoxMajorant Geometry.b3853 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3853.Widths)
  · have he : Geometry.b3853.half 0 false=Geometry.b4225 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4225
  · have he : Geometry.b3853.half 0 true=Geometry.b4226 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4226

theorem bound3852 : BoxMajorant Geometry.b3852 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3852.Widths)
  · have he : Geometry.b3852.half 0 false=Geometry.b4223 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4223
  · have he : Geometry.b3852.half 0 true=Geometry.b4224 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4224

theorem bound3851 : BoxMajorant Geometry.b3851 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3851 2 (by decide +kernel) x hx hd ho).elim

theorem bound3542 : BoxMajorant Geometry.b3542 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3542.Widths)
  · have he : Geometry.b3542.half 2 false=Geometry.b3855 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3855
  · have he : Geometry.b3542.half 2 true=Geometry.b3856 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3856

theorem bound3541 : BoxMajorant Geometry.b3541 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3541.Widths)
  · have he : Geometry.b3541.half 2 false=Geometry.b3853 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3853
  · have he : Geometry.b3541.half 2 true=Geometry.b3854 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3854

theorem bound3540 : BoxMajorant Geometry.b3540 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3540.Widths)
  · have he : Geometry.b3540.half 2 false=Geometry.b3851 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3851
  · have he : Geometry.b3540.half 2 true=Geometry.b3852 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3852

theorem bound3539 : BoxMajorant Geometry.b3539 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3539 2 (by decide +kernel) x hx hd ho).elim

theorem bound3268 : BoxMajorant Geometry.b3268 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3268.Widths)
  · have he : Geometry.b3268.half 1 false=Geometry.b3541 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3541
  · have he : Geometry.b3268.half 1 true=Geometry.b3542 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3542

theorem bound3267 : BoxMajorant Geometry.b3267 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3267.Widths)
  · have he : Geometry.b3267.half 1 false=Geometry.b3539 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3539
  · have he : Geometry.b3267.half 1 true=Geometry.b3540 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3540

theorem bound2940 : BoxMajorant Geometry.b2940 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2940.Widths)
  · have he : Geometry.b2940.half 0 false=Geometry.b3267 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3267
  · have he : Geometry.b2940.half 0 true=Geometry.b3268 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3268

end N7.Kernel.Cover
