import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverProofs.P0394
import N7.Kernel.CoverProofs.P0395
import N7.Kernel.CoverProofs.P0396
import N7.Kernel.CoverProofs.P0397
import N7.Kernel.CoverProofs.P0398
import N7.Kernel.CoverProofs.P0399
import N7.Kernel.PositiveGroups.G0332
import N7.Kernel.PositiveGroups.G0359
import N7.Kernel.PositiveGroups.G0390
import N7.Kernel.PositiveGroups.G0391
import N7.Kernel.PositiveGroups.G0411
import N7.Kernel.PositiveGroups.G0412
import N7.Kernel.PositiveGroups.G0429
import N7.Kernel.PositiveGroups.G0430
import N7.Kernel.PositiveGroups.G0443
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4699 : BoxMajorant Geometry.b4699 := by
  exact PositiveLeaves.L252.bound

theorem bound4698 : BoxMajorant Geometry.b4698 := by
  exact PositiveLeaves.L255.bound

theorem bound4696 : BoxMajorant Geometry.b4696 := by
  exact PositiveLeaves.L258.bound

theorem bound4691 : BoxMajorant Geometry.b4691 := by
  exact PositiveLeaves.L268.bound

theorem bound4428 : BoxMajorant Geometry.b4428 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4428.Widths)
  · have he : Geometry.b4428.half 1 false=Geometry.b4699 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4699
  · have he : Geometry.b4428.half 1 true=Geometry.b4700 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4700

theorem bound4427 : BoxMajorant Geometry.b4427 := by
  exact PositiveLeaves.L253.bound

theorem bound4426 : BoxMajorant Geometry.b4426 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4426.Widths)
  · have he : Geometry.b4426.half 1 false=Geometry.b4697 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4697
  · have he : Geometry.b4426.half 1 true=Geometry.b4698 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4698

theorem bound4425 : BoxMajorant Geometry.b4425 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4425.Widths)
  · have he : Geometry.b4425.half 1 false=Geometry.b4695 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4695
  · have he : Geometry.b4425.half 1 true=Geometry.b4696 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4696

theorem bound4424 : BoxMajorant Geometry.b4424 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4424.Widths)
  · have he : Geometry.b4424.half 1 false=Geometry.b4693 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4693
  · have he : Geometry.b4424.half 1 true=Geometry.b4694 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4694

theorem bound4423 : BoxMajorant Geometry.b4423 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4423.Widths)
  · have he : Geometry.b4423.half 1 false=Geometry.b4691 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4691
  · have he : Geometry.b4423.half 1 true=Geometry.b4692 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4692

theorem bound4130 : BoxMajorant Geometry.b4130 := by
  exact PositiveLeaves.L247.bound

theorem bound4129 : BoxMajorant Geometry.b4129 := by
  exact PositiveLeaves.L248.bound

theorem bound4128 : BoxMajorant Geometry.b4128 := by
  exact PositiveLeaves.L249.bound

theorem bound4127 : BoxMajorant Geometry.b4127 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4127.Widths)
  · have he : Geometry.b4127.half 0 false=Geometry.b4427 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4427
  · have he : Geometry.b4127.half 0 true=Geometry.b4428 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4428

theorem bound4126 : BoxMajorant Geometry.b4126 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4126.Widths)
  · have he : Geometry.b4126.half 0 false=Geometry.b4425 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4425
  · have he : Geometry.b4126.half 0 true=Geometry.b4426 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4426

theorem bound4125 : BoxMajorant Geometry.b4125 := by
  exact PositiveLeaves.L261.bound

theorem bound4124 : BoxMajorant Geometry.b4124 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4124.Widths)
  · have he : Geometry.b4124.half 0 false=Geometry.b4423 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4423
  · have he : Geometry.b4124.half 0 true=Geometry.b4424 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4424

theorem bound4123 : BoxMajorant Geometry.b4123 := by
  exact PositiveLeaves.L269.bound

theorem bound4122 : BoxMajorant Geometry.b4122 := by
  exact PositiveLeaves.L270.bound

theorem bound4121 : BoxMajorant Geometry.b4121 := by
  exact PositiveLeaves.L271.bound

theorem bound4120 : BoxMajorant Geometry.b4120 := by
  exact PositiveLeaves.L272.bound

theorem bound4119 : BoxMajorant Geometry.b4119 := by
  exact PositiveLeaves.L273.bound

theorem bound3716 : BoxMajorant Geometry.b3716 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3716.Widths)
  · have he : Geometry.b3716.half 2 false=Geometry.b4129 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4129
  · have he : Geometry.b3716.half 2 true=Geometry.b4130 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4130

theorem bound3715 : BoxMajorant Geometry.b3715 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3715.Widths)
  · have he : Geometry.b3715.half 2 false=Geometry.b4127 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4127
  · have he : Geometry.b3715.half 2 true=Geometry.b4128 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4128

theorem bound3714 : BoxMajorant Geometry.b3714 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3714.Widths)
  · have he : Geometry.b3714.half 2 false=Geometry.b4125 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4125
  · have he : Geometry.b3714.half 2 true=Geometry.b4126 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4126

theorem bound3713 : BoxMajorant Geometry.b3713 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3713.Widths)
  · have he : Geometry.b3713.half 2 false=Geometry.b4123 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4123
  · have he : Geometry.b3713.half 2 true=Geometry.b4124 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4124

theorem bound3712 : BoxMajorant Geometry.b3712 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3712.Widths)
  · have he : Geometry.b3712.half 2 false=Geometry.b4121 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4121
  · have he : Geometry.b3712.half 2 true=Geometry.b4122 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4122

theorem bound3711 : BoxMajorant Geometry.b3711 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3711.Widths)
  · have he : Geometry.b3711.half 2 false=Geometry.b4119 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4119
  · have he : Geometry.b3711.half 2 true=Geometry.b4120 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4120

theorem bound3444 : BoxMajorant Geometry.b3444 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3444.Widths)
  · have he : Geometry.b3444.half 1 false=Geometry.b3715 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3715
  · have he : Geometry.b3444.half 1 true=Geometry.b3716 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3716

theorem bound3443 : BoxMajorant Geometry.b3443 := by
  exact PositiveLeaves.L254.bound

theorem bound3442 : BoxMajorant Geometry.b3442 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3442.Widths)
  · have he : Geometry.b3442.half 1 false=Geometry.b3713 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3713
  · have he : Geometry.b3442.half 1 true=Geometry.b3714 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3714

theorem bound3441 : BoxMajorant Geometry.b3441 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3441.Widths)
  · have he : Geometry.b3441.half 1 false=Geometry.b3711 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3711
  · have he : Geometry.b3441.half 1 true=Geometry.b3712 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3712

theorem bound3158 : BoxMajorant Geometry.b3158 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3158.Widths)
  · have he : Geometry.b3158.half 0 false=Geometry.b3443 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3443
  · have he : Geometry.b3158.half 0 true=Geometry.b3444 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3444

theorem bound3157 : BoxMajorant Geometry.b3157 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3157.Widths)
  · have he : Geometry.b3157.half 0 false=Geometry.b3441 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3441
  · have he : Geometry.b3157.half 0 true=Geometry.b3442 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3442

theorem bound2763 : BoxMajorant Geometry.b2763 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2763.Widths)
  · have he : Geometry.b2763.half 2 false=Geometry.b3157 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3157
  · have he : Geometry.b2763.half 2 true=Geometry.b3158 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3158

end N7.Kernel.Cover
