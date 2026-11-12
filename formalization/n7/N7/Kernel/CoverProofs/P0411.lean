import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverProofs.P0419
import N7.Kernel.CoverProofs.P0420
import N7.Kernel.CoverProofs.P0421
import N7.Kernel.CoverProofs.P0422
import N7.Kernel.CoverProofs.P0423
import N7.Kernel.CoverProofs.P0424
import N7.Kernel.PositiveGroups.G0484
import N7.Kernel.PositiveGroups.G0489
import N7.Kernel.PositiveGroups.G0492
import N7.Kernel.PositiveGroups.G0493
import N7.Kernel.PositiveGroups.G0495
import N7.Kernel.PositiveGroups.G0496
import N7.Kernel.PositiveGroups.G0497
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5821 : BoxMajorant Geometry.b5821 := by
  exact PositiveLeaves.L393.bound

theorem bound5817 : BoxMajorant Geometry.b5817 := by
  exact PositiveLeaves.L408.bound

theorem bound5778 : BoxMajorant Geometry.b5778 := by
  exact PositiveLeaves.L375.bound

theorem bound5777 : BoxMajorant Geometry.b5777 := by
  exact PositiveLeaves.L376.bound

theorem bound5776 : BoxMajorant Geometry.b5776 := by
  exact PositiveLeaves.L377.bound

theorem bound5775 : BoxMajorant Geometry.b5775 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5775.Widths)
  · have he : Geometry.b5775.half 0 false=Geometry.b5823 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5823
  · have he : Geometry.b5775.half 0 true=Geometry.b5824 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5824

theorem bound5774 : BoxMajorant Geometry.b5774 := by
  exact PositiveLeaves.L386.bound

theorem bound5773 : BoxMajorant Geometry.b5773 := by
  exact PositiveLeaves.L387.bound

theorem bound5772 : BoxMajorant Geometry.b5772 := by
  exact PositiveLeaves.L388.bound

theorem bound5771 : BoxMajorant Geometry.b5771 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5771.Widths)
  · have he : Geometry.b5771.half 0 false=Geometry.b5821 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5821
  · have he : Geometry.b5771.half 0 true=Geometry.b5822 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5822

theorem bound5770 : BoxMajorant Geometry.b5770 := by
  exact PositiveLeaves.L395.bound

theorem bound5769 : BoxMajorant Geometry.b5769 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5769.Widths)
  · have he : Geometry.b5769.half 0 false=Geometry.b5819 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5819
  · have he : Geometry.b5769.half 0 true=Geometry.b5820 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5820

theorem bound5768 : BoxMajorant Geometry.b5768 := by
  exact PositiveLeaves.L404.bound

theorem bound5767 : BoxMajorant Geometry.b5767 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5767.Widths)
  · have he : Geometry.b5767.half 0 false=Geometry.b5817 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5817
  · have he : Geometry.b5767.half 0 true=Geometry.b5818 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5818

theorem bound5766 : BoxMajorant Geometry.b5766 := by
  exact PositiveLeaves.L409.bound

theorem bound5765 : BoxMajorant Geometry.b5765 := by
  exact PositiveLeaves.L410.bound

theorem bound5720 : BoxMajorant Geometry.b5720 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5720.Widths)
  · have he : Geometry.b5720.half 2 false=Geometry.b5777 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5777
  · have he : Geometry.b5720.half 2 true=Geometry.b5778 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5778

theorem bound5719 : BoxMajorant Geometry.b5719 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5719.Widths)
  · have he : Geometry.b5719.half 2 false=Geometry.b5775 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5775
  · have he : Geometry.b5719.half 2 true=Geometry.b5776 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5776

theorem bound5718 : BoxMajorant Geometry.b5718 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5718.Widths)
  · have he : Geometry.b5718.half 2 false=Geometry.b5773 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5773
  · have he : Geometry.b5718.half 2 true=Geometry.b5774 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5774

theorem bound5717 : BoxMajorant Geometry.b5717 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5717.Widths)
  · have he : Geometry.b5717.half 2 false=Geometry.b5771 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5771
  · have he : Geometry.b5717.half 2 true=Geometry.b5772 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5772

theorem bound5716 : BoxMajorant Geometry.b5716 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5716.Widths)
  · have he : Geometry.b5716.half 2 false=Geometry.b5769 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5769
  · have he : Geometry.b5716.half 2 true=Geometry.b5770 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5770

theorem bound5715 : BoxMajorant Geometry.b5715 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5715.Widths)
  · have he : Geometry.b5715.half 2 false=Geometry.b5767 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5767
  · have he : Geometry.b5715.half 2 true=Geometry.b5768 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5768

theorem bound5714 : BoxMajorant Geometry.b5714 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5714.Widths)
  · have he : Geometry.b5714.half 2 false=Geometry.b5765 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5765
  · have he : Geometry.b5714.half 2 true=Geometry.b5766 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5766

theorem bound5713 : BoxMajorant Geometry.b5713 := by
  exact PositiveLeaves.L411.bound

theorem bound5686 : BoxMajorant Geometry.b5686 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5686.Widths)
  · have he : Geometry.b5686.half 1 false=Geometry.b5719 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5719
  · have he : Geometry.b5686.half 1 true=Geometry.b5720 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5720

theorem bound5685 : BoxMajorant Geometry.b5685 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5685.Widths)
  · have he : Geometry.b5685.half 1 false=Geometry.b5717 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5717
  · have he : Geometry.b5685.half 1 true=Geometry.b5718 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5718

theorem bound5684 : BoxMajorant Geometry.b5684 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5684.Widths)
  · have he : Geometry.b5684.half 1 false=Geometry.b5715 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5715
  · have he : Geometry.b5684.half 1 true=Geometry.b5716 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5716

theorem bound5683 : BoxMajorant Geometry.b5683 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5683.Widths)
  · have he : Geometry.b5683.half 1 false=Geometry.b5713 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5713
  · have he : Geometry.b5683.half 1 true=Geometry.b5714 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5714

theorem bound5648 : BoxMajorant Geometry.b5648 := by
  exact PositiveLeaves.L374.bound

theorem bound5647 : BoxMajorant Geometry.b5647 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5647.Widths)
  · have he : Geometry.b5647.half 0 false=Geometry.b5685 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5685
  · have he : Geometry.b5647.half 0 true=Geometry.b5686 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5686

theorem bound5646 : BoxMajorant Geometry.b5646 := by
  exact PositiveLeaves.L394.bound

theorem bound5645 : BoxMajorant Geometry.b5645 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5645.Widths)
  · have he : Geometry.b5645.half 0 false=Geometry.b5683 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5683
  · have he : Geometry.b5645.half 0 true=Geometry.b5684 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5684

theorem bound5608 : BoxMajorant Geometry.b5608 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5608.Widths)
  · have he : Geometry.b5608.half 2 false=Geometry.b5647 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5647
  · have he : Geometry.b5608.half 2 true=Geometry.b5648 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5648

theorem bound5607 : BoxMajorant Geometry.b5607 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5607.Widths)
  · have he : Geometry.b5607.half 2 false=Geometry.b5645 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5645
  · have he : Geometry.b5607.half 2 true=Geometry.b5646 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5646

theorem bound5578 : BoxMajorant Geometry.b5578 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5578.Widths)
  · have he : Geometry.b5578.half 1 false=Geometry.b5607 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5607
  · have he : Geometry.b5578.half 1 true=Geometry.b5608 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5608

end N7.Kernel.Cover
