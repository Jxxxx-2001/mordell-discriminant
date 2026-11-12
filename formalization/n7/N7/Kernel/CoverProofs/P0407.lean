import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.PositiveGroups.G0484
import N7.Kernel.PositiveGroups.G0487
import N7.Kernel.PositiveGroups.G0488
import N7.Kernel.PositiveGroups.G0489
import N7.Kernel.PositiveGroups.G0491
import N7.Kernel.PositiveGroups.G0492
import N7.Kernel.PositiveGroups.G0495
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5784 : BoxMajorant Geometry.b5784 := by
  exact PositiveLeaves.L361.bound

theorem bound5783 : BoxMajorant Geometry.b5783 := by
  exact PositiveLeaves.L362.bound

theorem bound5782 : BoxMajorant Geometry.b5782 := by
  exact PositiveLeaves.L364.bound

theorem bound5781 : BoxMajorant Geometry.b5781 := by
  exact PositiveLeaves.L365.bound

theorem bound5780 : BoxMajorant Geometry.b5780 := by
  exact PositiveLeaves.L370.bound

theorem bound5779 : BoxMajorant Geometry.b5779 := by
  exact PositiveLeaves.L371.bound

theorem bound5726 : BoxMajorant Geometry.b5726 := by
  exact PositiveLeaves.L360.bound

theorem bound5725 : BoxMajorant Geometry.b5725 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5725.Widths)
  · have he : Geometry.b5725.half 2 false=Geometry.b5783 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5783
  · have he : Geometry.b5725.half 2 true=Geometry.b5784 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5784

theorem bound5724 : BoxMajorant Geometry.b5724 := by
  exact PositiveLeaves.L363.bound

theorem bound5723 : BoxMajorant Geometry.b5723 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5723.Widths)
  · have he : Geometry.b5723.half 2 false=Geometry.b5781 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5781
  · have he : Geometry.b5723.half 2 true=Geometry.b5782 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5782

theorem bound5722 : BoxMajorant Geometry.b5722 := by
  exact PositiveLeaves.L369.bound

theorem bound5721 : BoxMajorant Geometry.b5721 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5721.Widths)
  · have he : Geometry.b5721.half 2 false=Geometry.b5779 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5779
  · have he : Geometry.b5721.half 2 true=Geometry.b5780 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5780

theorem bound5690 : BoxMajorant Geometry.b5690 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5690.Widths)
  · have he : Geometry.b5690.half 1 false=Geometry.b5725 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5725
  · have he : Geometry.b5690.half 1 true=Geometry.b5726 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5726

theorem bound5689 : BoxMajorant Geometry.b5689 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5689.Widths)
  · have he : Geometry.b5689.half 1 false=Geometry.b5723 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5723
  · have he : Geometry.b5689.half 1 true=Geometry.b5724 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5724

theorem bound5688 : BoxMajorant Geometry.b5688 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5688.Widths)
  · have he : Geometry.b5688.half 1 false=Geometry.b5721 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5721
  · have he : Geometry.b5688.half 1 true=Geometry.b5722 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5722

theorem bound5687 : BoxMajorant Geometry.b5687 := by
  exact PositiveLeaves.L372.bound

theorem bound5656 : BoxMajorant Geometry.b5656 := by
  exact PositiveLeaves.L357.bound

theorem bound5655 : BoxMajorant Geometry.b5655 := by
  exact PositiveLeaves.L358.bound

theorem bound5654 : BoxMajorant Geometry.b5654 := by
  exact PositiveLeaves.L359.bound

theorem bound5653 : BoxMajorant Geometry.b5653 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5653.Widths)
  · have he : Geometry.b5653.half 0 false=Geometry.b5689 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5689
  · have he : Geometry.b5653.half 0 true=Geometry.b5690 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5690

theorem bound5652 : BoxMajorant Geometry.b5652 := by
  exact PositiveLeaves.L366.bound

theorem bound5651 : BoxMajorant Geometry.b5651 := by
  exact PositiveLeaves.L367.bound

theorem bound5650 : BoxMajorant Geometry.b5650 := by
  exact PositiveLeaves.L368.bound

theorem bound5649 : BoxMajorant Geometry.b5649 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5649.Widths)
  · have he : Geometry.b5649.half 0 false=Geometry.b5687 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5687
  · have he : Geometry.b5649.half 0 true=Geometry.b5688 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5688

theorem bound5612 : BoxMajorant Geometry.b5612 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5612.Widths)
  · have he : Geometry.b5612.half 2 false=Geometry.b5655 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5655
  · have he : Geometry.b5612.half 2 true=Geometry.b5656 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5656

theorem bound5611 : BoxMajorant Geometry.b5611 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5611.Widths)
  · have he : Geometry.b5611.half 2 false=Geometry.b5653 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5653
  · have he : Geometry.b5611.half 2 true=Geometry.b5654 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5654

theorem bound5610 : BoxMajorant Geometry.b5610 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5610.Widths)
  · have he : Geometry.b5610.half 2 false=Geometry.b5651 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5651
  · have he : Geometry.b5610.half 2 true=Geometry.b5652 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5652

theorem bound5609 : BoxMajorant Geometry.b5609 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5609.Widths)
  · have he : Geometry.b5609.half 2 false=Geometry.b5649 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5649
  · have he : Geometry.b5609.half 2 true=Geometry.b5650 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5650

theorem bound5580 : BoxMajorant Geometry.b5580 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5580.Widths)
  · have he : Geometry.b5580.half 1 false=Geometry.b5611 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5611
  · have he : Geometry.b5580.half 1 true=Geometry.b5612 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5612

theorem bound5579 : BoxMajorant Geometry.b5579 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5579.Widths)
  · have he : Geometry.b5579.half 1 false=Geometry.b5609 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5609
  · have he : Geometry.b5579.half 1 true=Geometry.b5610 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5610

theorem bound5518 : BoxMajorant Geometry.b5518 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5518.Widths)
  · have he : Geometry.b5518.half 0 false=Geometry.b5579 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5579
  · have he : Geometry.b5518.half 0 true=Geometry.b5580 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5580

end N7.Kernel.Cover
