import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0307
import N7.Kernel.PositiveGroups.G0329
import N7.Kernel.PositiveGroups.G0330
import N7.Kernel.PositiveGroups.G0356
import N7.Kernel.PositiveGroups.G0357
import N7.Kernel.PositiveGroups.G0358
import N7.Kernel.PositiveGroups.G0388
import N7.Kernel.PositiveGroups.G0389
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5498 : BoxMajorant Geometry.b5498 := by
  exact PositiveLeaves.L988.bound

theorem bound5497 : BoxMajorant Geometry.b5497 := by
  exact PositiveLeaves.L989.bound

theorem bound5366 : BoxMajorant Geometry.b5366 := by
  exact PositiveLeaves.L987.bound

theorem bound5365 : BoxMajorant Geometry.b5365 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5365.Widths)
  · have he : Geometry.b5365.half 2 false=Geometry.b5497 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5497
  · have he : Geometry.b5365.half 2 true=Geometry.b5498 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5498

theorem bound5258 : BoxMajorant Geometry.b5258 := by
  exact PositiveLeaves.L986.bound

theorem bound5257 : BoxMajorant Geometry.b5257 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5257.Widths)
  · have he : Geometry.b5257.half 1 false=Geometry.b5365 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5365
  · have he : Geometry.b5257.half 1 true=Geometry.b5366 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5366

theorem bound5048 : BoxMajorant Geometry.b5048 := by
  exact PositiveLeaves.L983.bound

theorem bound5047 : BoxMajorant Geometry.b5047 := by
  exact PositiveLeaves.L984.bound

theorem bound5046 : BoxMajorant Geometry.b5046 := by
  exact PositiveLeaves.L985.bound

theorem bound5045 : BoxMajorant Geometry.b5045 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5045.Widths)
  · have he : Geometry.b5045.half 0 false=Geometry.b5257 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5257
  · have he : Geometry.b5045.half 0 true=Geometry.b5258 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5258

theorem bound4676 : BoxMajorant Geometry.b4676 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4676.Widths)
  · have he : Geometry.b4676.half 2 false=Geometry.b5047 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5047
  · have he : Geometry.b4676.half 2 true=Geometry.b5048 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5048

theorem bound4675 : BoxMajorant Geometry.b4675 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4675.Widths)
  · have he : Geometry.b4675.half 2 false=Geometry.b5045 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5045
  · have he : Geometry.b4675.half 2 true=Geometry.b5046 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5046

theorem bound4410 : BoxMajorant Geometry.b4410 := by
  exact PositiveLeaves.L982.bound

theorem bound4409 : BoxMajorant Geometry.b4409 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4409.Widths)
  · have he : Geometry.b4409.half 1 false=Geometry.b4675 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4675
  · have he : Geometry.b4409.half 1 true=Geometry.b4676 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4676

theorem bound4076 : BoxMajorant Geometry.b4076 := by
  exact PositiveLeaves.L975.bound

theorem bound4075 : BoxMajorant Geometry.b4075 := by
  exact PositiveLeaves.L976.bound

theorem bound4074 : BoxMajorant Geometry.b4074 := by
  exact PositiveLeaves.L977.bound

theorem bound4073 : BoxMajorant Geometry.b4073 := by
  exact PositiveLeaves.L978.bound

theorem bound4072 : BoxMajorant Geometry.b4072 := by
  exact PositiveLeaves.L979.bound

theorem bound4071 : BoxMajorant Geometry.b4071 := by
  exact PositiveLeaves.L980.bound

theorem bound4070 : BoxMajorant Geometry.b4070 := by
  exact PositiveLeaves.L981.bound

theorem bound4069 : BoxMajorant Geometry.b4069 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4069.Widths)
  · have he : Geometry.b4069.half 0 false=Geometry.b4409 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4409
  · have he : Geometry.b4069.half 0 true=Geometry.b4410 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4410

theorem bound3674 : BoxMajorant Geometry.b3674 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3674.Widths)
  · have he : Geometry.b3674.half 2 false=Geometry.b4075 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4075
  · have he : Geometry.b3674.half 2 true=Geometry.b4076 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4076

theorem bound3673 : BoxMajorant Geometry.b3673 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3673.Widths)
  · have he : Geometry.b3673.half 2 false=Geometry.b4073 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4073
  · have he : Geometry.b3673.half 2 true=Geometry.b4074 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4074

theorem bound3672 : BoxMajorant Geometry.b3672 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3672.Widths)
  · have he : Geometry.b3672.half 2 false=Geometry.b4071 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4071
  · have he : Geometry.b3672.half 2 true=Geometry.b4072 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4072

theorem bound3671 : BoxMajorant Geometry.b3671 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3671.Widths)
  · have he : Geometry.b3671.half 2 false=Geometry.b4069 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4069
  · have he : Geometry.b3671.half 2 true=Geometry.b4070 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4070

theorem bound3408 : BoxMajorant Geometry.b3408 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3408.Widths)
  · have he : Geometry.b3408.half 1 false=Geometry.b3673 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3673
  · have he : Geometry.b3408.half 1 true=Geometry.b3674 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3674

theorem bound3407 : BoxMajorant Geometry.b3407 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3407.Widths)
  · have he : Geometry.b3407.half 1 false=Geometry.b3671 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3671
  · have he : Geometry.b3407.half 1 true=Geometry.b3672 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3672

theorem bound3075 : BoxMajorant Geometry.b3075 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3075.Widths)
  · have he : Geometry.b3075.half 0 false=Geometry.b3407 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3407
  · have he : Geometry.b3075.half 0 true=Geometry.b3408 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3408

end N7.Kernel.Cover
