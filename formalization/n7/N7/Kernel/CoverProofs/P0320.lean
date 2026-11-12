import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.PositiveGroups.G0309
import N7.Kernel.PositiveGroups.G0333
import N7.Kernel.PositiveGroups.G0362
import N7.Kernel.PositiveGroups.G0363
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4102 : BoxMajorant Geometry.b4102 := by
  exact PositiveLeaves.L475.bound

theorem bound4101 : BoxMajorant Geometry.b4101 := by
  exact PositiveLeaves.L476.bound

theorem bound4100 : BoxMajorant Geometry.b4100 := by
  exact PositiveLeaves.L477.bound

theorem bound4099 : BoxMajorant Geometry.b4099 := by
  exact PositiveLeaves.L478.bound

theorem bound4098 : BoxMajorant Geometry.b4098 := by
  exact PositiveLeaves.L479.bound

theorem bound4097 : BoxMajorant Geometry.b4097 := by
  exact PositiveLeaves.L480.bound

theorem bound3700 : BoxMajorant Geometry.b3700 := by
  exact PositiveLeaves.L472.bound

theorem bound3699 : BoxMajorant Geometry.b3699 := by
  exact PositiveLeaves.L473.bound

theorem bound3698 : BoxMajorant Geometry.b3698 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3698.Widths)
  · have he : Geometry.b3698.half 2 false=Geometry.b4101 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4101
  · have he : Geometry.b3698.half 2 true=Geometry.b4102 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4102

theorem bound3697 : BoxMajorant Geometry.b3697 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3697.Widths)
  · have he : Geometry.b3697.half 2 false=Geometry.b4099 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4099
  · have he : Geometry.b3697.half 2 true=Geometry.b4100 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4100

theorem bound3696 : BoxMajorant Geometry.b3696 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3696.Widths)
  · have he : Geometry.b3696.half 2 false=Geometry.b4097 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4097
  · have he : Geometry.b3696.half 2 true=Geometry.b4098 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4098

theorem bound3695 : BoxMajorant Geometry.b3695 := by
  exact PositiveLeaves.L481.bound

theorem bound3432 : BoxMajorant Geometry.b3432 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3432.Widths)
  · have he : Geometry.b3432.half 1 false=Geometry.b3699 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3699
  · have he : Geometry.b3432.half 1 true=Geometry.b3700 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3700

theorem bound3431 : BoxMajorant Geometry.b3431 := by
  exact PositiveLeaves.L474.bound

theorem bound3430 : BoxMajorant Geometry.b3430 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3430.Widths)
  · have he : Geometry.b3430.half 1 false=Geometry.b3697 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3697
  · have he : Geometry.b3430.half 1 true=Geometry.b3698 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3698

theorem bound3429 : BoxMajorant Geometry.b3429 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3429.Widths)
  · have he : Geometry.b3429.half 1 false=Geometry.b3695 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3695
  · have he : Geometry.b3429.half 1 true=Geometry.b3696 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3696

theorem bound3152 : BoxMajorant Geometry.b3152 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3152.Widths)
  · have he : Geometry.b3152.half 0 false=Geometry.b3431 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3431
  · have he : Geometry.b3152.half 0 true=Geometry.b3432 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3432

theorem bound3151 : BoxMajorant Geometry.b3151 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3151.Widths)
  · have he : Geometry.b3151.half 0 false=Geometry.b3429 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3429
  · have he : Geometry.b3151.half 0 true=Geometry.b3430 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3430

theorem bound2758 : BoxMajorant Geometry.b2758 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2758.Widths)
  · have he : Geometry.b2758.half 2 false=Geometry.b3151 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3151
  · have he : Geometry.b2758.half 2 true=Geometry.b3152 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3152

end N7.Kernel.Cover
