import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverGeometry.G0092
import N7.Kernel.PositiveGroups.G0483
import N7.Kernel.PositiveGroups.G0489
import N7.Kernel.PositiveGroups.G0493
import N7.Kernel.PositiveGroups.G0494
import N7.Kernel.PositiveGroups.G0499
import N7.Kernel.PositiveGroups.G0500
import N7.Kernel.PositiveGroups.G0505
import N7.Kernel.PositiveGroups.G0506
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5922 : BoxMajorant Geometry.b5922 := by
  exact PositiveLeaves.L314.bound

theorem bound5921 : BoxMajorant Geometry.b5921 := by
  exact PositiveLeaves.L315.bound

theorem bound5920 : BoxMajorant Geometry.b5920 := by
  exact PositiveLeaves.L316.bound

theorem bound5919 : BoxMajorant Geometry.b5919 := by
  exact PositiveLeaves.L317.bound

theorem bound5918 : BoxMajorant Geometry.b5918 := by
  exact PositiveLeaves.L318.bound

theorem bound5917 : BoxMajorant Geometry.b5917 := by
  exact PositiveLeaves.L319.bound

theorem bound5872 : BoxMajorant Geometry.b5872 := by
  exact PositiveLeaves.L313.bound

theorem bound5871 : BoxMajorant Geometry.b5871 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5871.Widths)
  · have he : Geometry.b5871.half 2 false=Geometry.b5921 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5921
  · have he : Geometry.b5871.half 2 true=Geometry.b5922 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5922

theorem bound5870 : BoxMajorant Geometry.b5870 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5870.Widths)
  · have he : Geometry.b5870.half 2 false=Geometry.b5919 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5919
  · have he : Geometry.b5870.half 2 true=Geometry.b5920 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5920

theorem bound5869 : BoxMajorant Geometry.b5869 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5869.Widths)
  · have he : Geometry.b5869.half 2 false=Geometry.b5917 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5917
  · have he : Geometry.b5869.half 2 true=Geometry.b5918 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5918

theorem bound5834 : BoxMajorant Geometry.b5834 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5834.Widths)
  · have he : Geometry.b5834.half 1 false=Geometry.b5871 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5871
  · have he : Geometry.b5834.half 1 true=Geometry.b5872 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5872

theorem bound5833 : BoxMajorant Geometry.b5833 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5833.Widths)
  · have he : Geometry.b5833.half 1 false=Geometry.b5869 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5869
  · have he : Geometry.b5833.half 1 true=Geometry.b5870 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5870

theorem bound5800 : BoxMajorant Geometry.b5800 := by
  exact PositiveLeaves.L308.bound

theorem bound5799 : BoxMajorant Geometry.b5799 := by
  exact PositiveLeaves.L309.bound

theorem bound5798 : BoxMajorant Geometry.b5798 := by
  exact PositiveLeaves.L310.bound

theorem bound5797 : BoxMajorant Geometry.b5797 := by
  exact PositiveLeaves.L311.bound

theorem bound5796 : BoxMajorant Geometry.b5796 := by
  exact PositiveLeaves.L312.bound

theorem bound5795 : BoxMajorant Geometry.b5795 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5795.Widths)
  · have he : Geometry.b5795.half 0 false=Geometry.b5833 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5833
  · have he : Geometry.b5795.half 0 true=Geometry.b5834 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5834

theorem bound5736 : BoxMajorant Geometry.b5736 := by
  exact PositiveLeaves.L307.bound

theorem bound5735 : BoxMajorant Geometry.b5735 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5735.Widths)
  · have he : Geometry.b5735.half 2 false=Geometry.b5799 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5799
  · have he : Geometry.b5735.half 2 true=Geometry.b5800 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5800

theorem bound5734 : BoxMajorant Geometry.b5734 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5734.Widths)
  · have he : Geometry.b5734.half 2 false=Geometry.b5797 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5797
  · have he : Geometry.b5734.half 2 true=Geometry.b5798 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5798

theorem bound5733 : BoxMajorant Geometry.b5733 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5733.Widths)
  · have he : Geometry.b5733.half 2 false=Geometry.b5795 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5795
  · have he : Geometry.b5733.half 2 true=Geometry.b5796 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5796

theorem bound5696 : BoxMajorant Geometry.b5696 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5696.Widths)
  · have he : Geometry.b5696.half 1 false=Geometry.b5735 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5735
  · have he : Geometry.b5696.half 1 true=Geometry.b5736 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5736

theorem bound5695 : BoxMajorant Geometry.b5695 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5695.Widths)
  · have he : Geometry.b5695.half 1 false=Geometry.b5733 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5733
  · have he : Geometry.b5695.half 1 true=Geometry.b5734 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5734

theorem bound5662 : BoxMajorant Geometry.b5662 := by
  exact PositiveLeaves.L306.bound

theorem bound5661 : BoxMajorant Geometry.b5661 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5661.Widths)
  · have he : Geometry.b5661.half 0 false=Geometry.b5695 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5695
  · have he : Geometry.b5661.half 0 true=Geometry.b5696 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5696

theorem bound5616 : BoxMajorant Geometry.b5616 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5616.Widths)
  · have he : Geometry.b5616.half 2 false=Geometry.b5661 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5661
  · have he : Geometry.b5616.half 2 true=Geometry.b5662 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5662

end N7.Kernel.Cover
