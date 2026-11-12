import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.PositiveGroups.G0308
import N7.Kernel.PositiveGroups.G0359
import N7.Kernel.PositiveGroups.G0391
import N7.Kernel.PositiveGroups.G0392
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4136 : BoxMajorant Geometry.b4136 := by
  exact PositiveLeaves.L241.bound

theorem bound4135 : BoxMajorant Geometry.b4135 := by
  exact PositiveLeaves.L242.bound

theorem bound4134 : BoxMajorant Geometry.b4134 := by
  exact PositiveLeaves.L243.bound

theorem bound4133 : BoxMajorant Geometry.b4133 := by
  exact PositiveLeaves.L244.bound

theorem bound4132 : BoxMajorant Geometry.b4132 := by
  exact PositiveLeaves.L245.bound

theorem bound4131 : BoxMajorant Geometry.b4131 := by
  exact PositiveLeaves.L246.bound

theorem bound3720 : BoxMajorant Geometry.b3720 := by
  exact PositiveLeaves.L240.bound

theorem bound3719 : BoxMajorant Geometry.b3719 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3719.Widths)
  · have he : Geometry.b3719.half 2 false=Geometry.b4135 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4135
  · have he : Geometry.b3719.half 2 true=Geometry.b4136 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4136

theorem bound3718 : BoxMajorant Geometry.b3718 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3718.Widths)
  · have he : Geometry.b3718.half 2 false=Geometry.b4133 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4133
  · have he : Geometry.b3718.half 2 true=Geometry.b4134 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4134

theorem bound3717 : BoxMajorant Geometry.b3717 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3717.Widths)
  · have he : Geometry.b3717.half 2 false=Geometry.b4131 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4131
  · have he : Geometry.b3717.half 2 true=Geometry.b4132 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4132

theorem bound3446 : BoxMajorant Geometry.b3446 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3446.Widths)
  · have he : Geometry.b3446.half 1 false=Geometry.b3719 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3719
  · have he : Geometry.b3446.half 1 true=Geometry.b3720 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3720

theorem bound3445 : BoxMajorant Geometry.b3445 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3445.Widths)
  · have he : Geometry.b3445.half 1 false=Geometry.b3717 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3717
  · have he : Geometry.b3445.half 1 true=Geometry.b3718 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3718

theorem bound3160 : BoxMajorant Geometry.b3160 := by
  exact PositiveLeaves.L239.bound

theorem bound3159 : BoxMajorant Geometry.b3159 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3159.Widths)
  · have he : Geometry.b3159.half 0 false=Geometry.b3445 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3445
  · have he : Geometry.b3159.half 0 true=Geometry.b3446 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3446

theorem bound2764 : BoxMajorant Geometry.b2764 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2764.Widths)
  · have he : Geometry.b2764.half 2 false=Geometry.b3159 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3159
  · have he : Geometry.b2764.half 2 true=Geometry.b3160 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3160

end N7.Kernel.Cover
