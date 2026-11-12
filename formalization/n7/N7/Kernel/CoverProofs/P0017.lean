import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0004
import N7.Kernel.CoverGeometry.G0006
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverProofs.P0136
import N7.Kernel.CoverProofs.P0137
import N7.Kernel.CoverProofs.P0138
import N7.Kernel.CoverProofs.P0139
import N7.Kernel.CoverProofs.P0140
import N7.Kernel.CoverProofs.P0141
import N7.Kernel.CoverProofs.P0142
import N7.Kernel.CoverProofs.P0143
import N7.Kernel.CoverProofs.P0144
import N7.Kernel.CoverProofs.P0145
import N7.Kernel.CoverProofs.P0146
import N7.Kernel.CoverProofs.P0147
import N7.Kernel.CoverProofs.P0148
import N7.Kernel.CoverProofs.P0149
import N7.Kernel.CoverProofs.P0150
import N7.Kernel.PositiveGroups.G0029
import N7.Kernel.PositiveGroups.G0052
import N7.Kernel.PositiveGroups.G0053
import N7.Kernel.PositiveGroups.G0080
import N7.Kernel.PositiveGroups.G0081
import N7.Kernel.PositiveGroups.G0082
import N7.Kernel.PositiveGroups.G0118
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound675 : BoxMajorant Geometry.b675 := by
  exact PositiveLeaves.L583.bound

theorem bound673 : BoxMajorant Geometry.b673 := by
  exact PositiveLeaves.L592.bound

theorem bound671 : BoxMajorant Geometry.b671 := by
  exact PositiveLeaves.L599.bound

theorem bound668 : BoxMajorant Geometry.b668 := by
  exact PositiveLeaves.L613.bound

theorem bound667 : BoxMajorant Geometry.b667 := by
  exact PositiveLeaves.L614.bound

theorem bound666 : BoxMajorant Geometry.b666 := by
  exact PositiveLeaves.L616.bound

theorem bound665 : BoxMajorant Geometry.b665 := by
  exact PositiveLeaves.L617.bound

theorem bound658 : BoxMajorant Geometry.b658 := by
  exact PositiveLeaves.L717.bound

theorem bound655 : BoxMajorant Geometry.b655 := by
  exact PositiveLeaves.L741.bound

theorem bound654 : BoxMajorant Geometry.b654 := by
  exact PositiveLeaves.L742.bound

theorem bound653 : BoxMajorant Geometry.b653 := by
  exact PositiveLeaves.L743.bound

theorem bound651 : BoxMajorant Geometry.b651 := by
  exact PositiveLeaves.L751.bound

theorem bound649 : BoxMajorant Geometry.b649 := by
  exact PositiveLeaves.L762.bound

theorem bound430 : BoxMajorant Geometry.b430 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b430.Widths)
  · have he : Geometry.b430.half 2 false=Geometry.b675 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound675
  · have he : Geometry.b430.half 2 true=Geometry.b676 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound676

theorem bound429 : BoxMajorant Geometry.b429 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b429.Widths)
  · have he : Geometry.b429.half 2 false=Geometry.b673 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound673
  · have he : Geometry.b429.half 2 true=Geometry.b674 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound674

theorem bound428 : BoxMajorant Geometry.b428 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b428.Widths)
  · have he : Geometry.b428.half 2 false=Geometry.b671 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound671
  · have he : Geometry.b428.half 2 true=Geometry.b672 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound672

theorem bound427 : BoxMajorant Geometry.b427 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b427.Widths)
  · have he : Geometry.b427.half 2 false=Geometry.b669 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound669
  · have he : Geometry.b427.half 2 true=Geometry.b670 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound670

theorem bound426 : BoxMajorant Geometry.b426 := by
  exact PositiveLeaves.L612.bound

theorem bound425 : BoxMajorant Geometry.b425 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b425.Widths)
  · have he : Geometry.b425.half 2 false=Geometry.b667 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound667
  · have he : Geometry.b425.half 2 true=Geometry.b668 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound668

theorem bound424 : BoxMajorant Geometry.b424 := by
  exact PositiveLeaves.L615.bound

theorem bound423 : BoxMajorant Geometry.b423 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b423.Widths)
  · have he : Geometry.b423.half 2 false=Geometry.b665 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound665
  · have he : Geometry.b423.half 2 true=Geometry.b666 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound666

theorem bound422 : BoxMajorant Geometry.b422 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b422.Widths)
  · have he : Geometry.b422.half 2 false=Geometry.b663 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound663
  · have he : Geometry.b422.half 2 true=Geometry.b664 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound664

theorem bound421 : BoxMajorant Geometry.b421 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b421.Widths)
  · have he : Geometry.b421.half 2 false=Geometry.b661 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound661
  · have he : Geometry.b421.half 2 true=Geometry.b662 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound662

theorem bound420 : BoxMajorant Geometry.b420 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b420.Widths)
  · have he : Geometry.b420.half 2 false=Geometry.b659 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound659
  · have he : Geometry.b420.half 2 true=Geometry.b660 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound660

theorem bound419 : BoxMajorant Geometry.b419 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b419.Widths)
  · have he : Geometry.b419.half 2 false=Geometry.b657 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound657
  · have he : Geometry.b419.half 2 true=Geometry.b658 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound658

theorem bound418 : BoxMajorant Geometry.b418 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b418.Widths)
  · have he : Geometry.b418.half 2 false=Geometry.b655 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound655
  · have he : Geometry.b418.half 2 true=Geometry.b656 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound656

theorem bound417 : BoxMajorant Geometry.b417 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b417.Widths)
  · have he : Geometry.b417.half 2 false=Geometry.b653 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound653
  · have he : Geometry.b417.half 2 true=Geometry.b654 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound654

theorem bound416 : BoxMajorant Geometry.b416 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b416.Widths)
  · have he : Geometry.b416.half 2 false=Geometry.b651 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound651
  · have he : Geometry.b416.half 2 true=Geometry.b652 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound652

theorem bound415 : BoxMajorant Geometry.b415 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b415.Widths)
  · have he : Geometry.b415.half 2 false=Geometry.b649 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound649
  · have he : Geometry.b415.half 2 true=Geometry.b650 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound650

theorem bound272 : BoxMajorant Geometry.b272 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b272.Widths)
  · have he : Geometry.b272.half 1 false=Geometry.b429 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound429
  · have he : Geometry.b272.half 1 true=Geometry.b430 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound430

theorem bound271 : BoxMajorant Geometry.b271 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b271.Widths)
  · have he : Geometry.b271.half 1 false=Geometry.b427 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound427
  · have he : Geometry.b271.half 1 true=Geometry.b428 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound428

theorem bound270 : BoxMajorant Geometry.b270 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b270.Widths)
  · have he : Geometry.b270.half 1 false=Geometry.b425 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound425
  · have he : Geometry.b270.half 1 true=Geometry.b426 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound426

theorem bound269 : BoxMajorant Geometry.b269 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b269.Widths)
  · have he : Geometry.b269.half 1 false=Geometry.b423 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound423
  · have he : Geometry.b269.half 1 true=Geometry.b424 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound424

theorem bound268 : BoxMajorant Geometry.b268 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b268.Widths)
  · have he : Geometry.b268.half 1 false=Geometry.b421 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound421
  · have he : Geometry.b268.half 1 true=Geometry.b422 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound422

theorem bound267 : BoxMajorant Geometry.b267 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b267.Widths)
  · have he : Geometry.b267.half 1 false=Geometry.b419 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound419
  · have he : Geometry.b267.half 1 true=Geometry.b420 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound420

theorem bound266 : BoxMajorant Geometry.b266 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b266.Widths)
  · have he : Geometry.b266.half 1 false=Geometry.b417 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound417
  · have he : Geometry.b266.half 1 true=Geometry.b418 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound418

theorem bound265 : BoxMajorant Geometry.b265 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b265.Widths)
  · have he : Geometry.b265.half 1 false=Geometry.b415 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound415
  · have he : Geometry.b265.half 1 true=Geometry.b416 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound416

theorem bound164 : BoxMajorant Geometry.b164 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b164.Widths)
  · have he : Geometry.b164.half 0 false=Geometry.b271 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound271
  · have he : Geometry.b164.half 0 true=Geometry.b272 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound272

theorem bound163 : BoxMajorant Geometry.b163 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b163.Widths)
  · have he : Geometry.b163.half 0 false=Geometry.b269 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound269
  · have he : Geometry.b163.half 0 true=Geometry.b270 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound270

theorem bound162 : BoxMajorant Geometry.b162 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b162.Widths)
  · have he : Geometry.b162.half 0 false=Geometry.b267 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound267
  · have he : Geometry.b162.half 0 true=Geometry.b268 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound268

theorem bound161 : BoxMajorant Geometry.b161 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b161.Widths)
  · have he : Geometry.b161.half 0 false=Geometry.b265 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound265
  · have he : Geometry.b161.half 0 true=Geometry.b266 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound266

theorem bound94 : BoxMajorant Geometry.b94 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b94.Widths)
  · have he : Geometry.b94.half 2 false=Geometry.b163 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound163
  · have he : Geometry.b94.half 2 true=Geometry.b164 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound164

theorem bound93 : BoxMajorant Geometry.b93 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b93.Widths)
  · have he : Geometry.b93.half 2 false=Geometry.b161 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound161
  · have he : Geometry.b93.half 2 true=Geometry.b162 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound162

theorem bound50 : BoxMajorant Geometry.b50 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b50.Widths)
  · have he : Geometry.b50.half 1 false=Geometry.b93 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound93
  · have he : Geometry.b50.half 1 true=Geometry.b94 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound94

end N7.Kernel.Cover
