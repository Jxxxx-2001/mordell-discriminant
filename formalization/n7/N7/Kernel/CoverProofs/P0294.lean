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
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverProofs.P0385
import N7.Kernel.CoverProofs.P0386
import N7.Kernel.PositiveGroups.G0283
import N7.Kernel.PositiveGroups.G0307
import N7.Kernel.PositiveGroups.G0330
import N7.Kernel.PositiveGroups.G0331
import N7.Kernel.PositiveGroups.G0358
import N7.Kernel.PositiveGroups.G0389
import N7.Kernel.PositiveGroups.G0411
import N7.Kernel.PositiveGroups.G0428
import N7.Kernel.PositiveGroups.G0429
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5636 : BoxMajorant Geometry.b5636 := by
  exact PositiveLeaves.L1003.bound

theorem bound5635 : BoxMajorant Geometry.b5635 := by
  exact PositiveLeaves.L1004.bound

theorem bound5634 : BoxMajorant Geometry.b5634 := by
  exact PositiveLeaves.L1007.bound

theorem bound5632 : BoxMajorant Geometry.b5632 := by
  exact PositiveLeaves.L1016.bound

theorem bound5600 : BoxMajorant Geometry.b5600 := by
  exact PositiveLeaves.L1002.bound

theorem bound5599 : BoxMajorant Geometry.b5599 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5599.Widths)
  · have he : Geometry.b5599.half 2 false=Geometry.b5635 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5635
  · have he : Geometry.b5599.half 2 true=Geometry.b5636 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5636

theorem bound5598 : BoxMajorant Geometry.b5598 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5598.Widths)
  · have he : Geometry.b5598.half 2 false=Geometry.b5633 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5633
  · have he : Geometry.b5598.half 2 true=Geometry.b5634 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5634

theorem bound5597 : BoxMajorant Geometry.b5597 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5597.Widths)
  · have he : Geometry.b5597.half 2 false=Geometry.b5631 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5631
  · have he : Geometry.b5597.half 2 true=Geometry.b5632 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5632

theorem bound5572 : BoxMajorant Geometry.b5572 := by
  exact PositiveLeaves.L1001.bound

theorem bound5571 : BoxMajorant Geometry.b5571 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5571.Widths)
  · have he : Geometry.b5571.half 1 false=Geometry.b5599 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5599
  · have he : Geometry.b5571.half 1 true=Geometry.b5600 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5600

theorem bound5570 : BoxMajorant Geometry.b5570 := by
  exact PositiveLeaves.L1006.bound

theorem bound5569 : BoxMajorant Geometry.b5569 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5569.Widths)
  · have he : Geometry.b5569.half 1 false=Geometry.b5597 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5597
  · have he : Geometry.b5569.half 1 true=Geometry.b5598 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5598

theorem bound5496 : BoxMajorant Geometry.b5496 := by
  exact PositiveLeaves.L1000.bound

theorem bound5495 : BoxMajorant Geometry.b5495 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5495.Widths)
  · have he : Geometry.b5495.half 0 false=Geometry.b5571 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5571
  · have he : Geometry.b5495.half 0 true=Geometry.b5572 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5572

theorem bound5494 : BoxMajorant Geometry.b5494 := by
  exact PositiveLeaves.L1005.bound

theorem bound5493 : BoxMajorant Geometry.b5493 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5493.Widths)
  · have he : Geometry.b5493.half 0 false=Geometry.b5569 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5569
  · have he : Geometry.b5493.half 0 true=Geometry.b5570 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5570

theorem bound5364 : BoxMajorant Geometry.b5364 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5364.Widths)
  · have he : Geometry.b5364.half 2 false=Geometry.b5495 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5495
  · have he : Geometry.b5364.half 2 true=Geometry.b5496 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5496

theorem bound5363 : BoxMajorant Geometry.b5363 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5363.Widths)
  · have he : Geometry.b5363.half 2 false=Geometry.b5493 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5493
  · have he : Geometry.b5363.half 2 true=Geometry.b5494 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5494

theorem bound5256 : BoxMajorant Geometry.b5256 := by
  exact PositiveLeaves.L999.bound

theorem bound5255 : BoxMajorant Geometry.b5255 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5255.Widths)
  · have he : Geometry.b5255.half 1 false=Geometry.b5363 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5363
  · have he : Geometry.b5255.half 1 true=Geometry.b5364 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5364

theorem bound5044 : BoxMajorant Geometry.b5044 := by
  exact PositiveLeaves.L998.bound

theorem bound5043 : BoxMajorant Geometry.b5043 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5043.Widths)
  · have he : Geometry.b5043.half 0 false=Geometry.b5255 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5255
  · have he : Geometry.b5043.half 0 true=Geometry.b5256 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5256

theorem bound4674 : BoxMajorant Geometry.b4674 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4674.Widths)
  · have he : Geometry.b4674.half 2 false=Geometry.b5043 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5043
  · have he : Geometry.b4674.half 2 true=Geometry.b5044 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5044

theorem bound4673 : BoxMajorant Geometry.b4673 := by
  exact PositiveLeaves.L1025.bound

theorem bound4408 : BoxMajorant Geometry.b4408 := by
  exact PositiveLeaves.L997.bound

theorem bound4407 : BoxMajorant Geometry.b4407 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4407.Widths)
  · have he : Geometry.b4407.half 1 false=Geometry.b4673 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4673
  · have he : Geometry.b4407.half 1 true=Geometry.b4674 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4674

theorem bound4068 : BoxMajorant Geometry.b4068 := by
  exact PositiveLeaves.L996.bound

theorem bound4067 : BoxMajorant Geometry.b4067 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4067.Widths)
  · have he : Geometry.b4067.half 0 false=Geometry.b4407 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4407
  · have he : Geometry.b4067.half 0 true=Geometry.b4408 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4408

theorem bound4066 : BoxMajorant Geometry.b4066 := by
  exact PositiveLeaves.L1026.bound

theorem bound4065 : BoxMajorant Geometry.b4065 := by
  exact PositiveLeaves.L1027.bound

theorem bound3670 : BoxMajorant Geometry.b3670 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3670.Widths)
  · have he : Geometry.b3670.half 2 false=Geometry.b4067 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4067
  · have he : Geometry.b3670.half 2 true=Geometry.b4068 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4068

theorem bound3669 : BoxMajorant Geometry.b3669 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3669.Widths)
  · have he : Geometry.b3669.half 2 false=Geometry.b4065 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4065
  · have he : Geometry.b3669.half 2 true=Geometry.b4066 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4066

theorem bound3406 : BoxMajorant Geometry.b3406 := by
  exact PositiveLeaves.L995.bound

theorem bound3405 : BoxMajorant Geometry.b3405 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3405.Widths)
  · have he : Geometry.b3405.half 1 false=Geometry.b3669 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3669
  · have he : Geometry.b3405.half 1 true=Geometry.b3670 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3670

theorem bound3073 : BoxMajorant Geometry.b3073 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3073.Widths)
  · have he : Geometry.b3073.half 0 false=Geometry.b3405 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3405
  · have he : Geometry.b3073.half 0 true=Geometry.b3406 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3406

end N7.Kernel.Cover
