import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.LocalBridge
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverGeometry.G0092
import N7.Kernel.CoverProofs.P0425
import N7.Kernel.Local.C1LargeMajorant
import N7.Kernel.PositiveGroups.G0483
import N7.Kernel.PositiveGroups.G0489
import N7.Kernel.PositiveGroups.G0490
import N7.Kernel.PositiveGroups.G0491
import N7.Kernel.PositiveGroups.G0497
import N7.Kernel.PositiveGroups.G0500
import N7.Kernel.PositiveGroups.G0501
import N7.Kernel.PositiveGroups.G0505
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5916 : BoxMajorant Geometry.b5916 := by
  exact PositiveLeaves.L323.bound

theorem bound5915 : BoxMajorant Geometry.b5915 := by
  exact PositiveLeaves.L324.bound

theorem bound5914 : BoxMajorant Geometry.b5914 := by
  exact PositiveLeaves.L325.bound

theorem bound5913 : BoxMajorant Geometry.b5913 := by
  exact PositiveLeaves.L326.bound

theorem bound5912 : BoxMajorant Geometry.b5912 := by
  exact PositiveLeaves.L332.bound

theorem bound5911 : BoxMajorant Geometry.b5911 := by
  exact PositiveLeaves.L333.bound

theorem bound5910 : BoxMajorant Geometry.b5910 := by
  exact PositiveLeaves.L335.bound

theorem bound5868 : BoxMajorant Geometry.b5868 := by
  exact PositiveLeaves.L322.bound

theorem bound5867 : BoxMajorant Geometry.b5867 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5867.Widths)
  · have he : Geometry.b5867.half 2 false=Geometry.b5915 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5915
  · have he : Geometry.b5867.half 2 true=Geometry.b5916 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5916

theorem bound5866 : BoxMajorant Geometry.b5866 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5866.Widths)
  · have he : Geometry.b5866.half 2 false=Geometry.b5913 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5913
  · have he : Geometry.b5866.half 2 true=Geometry.b5914 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5914

theorem bound5865 : BoxMajorant Geometry.b5865 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5865 Local.C1.center Local.C1.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C1.large_near_majorant hn

theorem bound5864 : BoxMajorant Geometry.b5864 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5864.Widths)
  · have he : Geometry.b5864.half 2 false=Geometry.b5911 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5911
  · have he : Geometry.b5864.half 2 true=Geometry.b5912 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5912

theorem bound5863 : BoxMajorant Geometry.b5863 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5863 Local.C1.center Local.C1.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C1.large_near_majorant hn

theorem bound5862 : BoxMajorant Geometry.b5862 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5862.Widths)
  · have he : Geometry.b5862.half 2 false=Geometry.b5909 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5909
  · have he : Geometry.b5862.half 2 true=Geometry.b5910 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5910

theorem bound5861 : BoxMajorant Geometry.b5861 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5861 Local.C1.center Local.C1.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C1.large_near_majorant hn

theorem bound5832 : BoxMajorant Geometry.b5832 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5832.Widths)
  · have he : Geometry.b5832.half 1 false=Geometry.b5867 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5867
  · have he : Geometry.b5832.half 1 true=Geometry.b5868 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5868

theorem bound5831 : BoxMajorant Geometry.b5831 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5831.Widths)
  · have he : Geometry.b5831.half 1 false=Geometry.b5865 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5865
  · have he : Geometry.b5831.half 1 true=Geometry.b5866 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5866

theorem bound5830 : BoxMajorant Geometry.b5830 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5830 0 (by decide +kernel) x hx hd ho).elim

theorem bound5829 : BoxMajorant Geometry.b5829 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5829 Local.C1.center Local.C1.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C1.large_near_majorant hn

theorem bound5828 : BoxMajorant Geometry.b5828 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5828.Widths)
  · have he : Geometry.b5828.half 1 false=Geometry.b5863 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5863
  · have he : Geometry.b5828.half 1 true=Geometry.b5864 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5864

theorem bound5827 : BoxMajorant Geometry.b5827 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5827.Widths)
  · have he : Geometry.b5827.half 1 false=Geometry.b5861 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5861
  · have he : Geometry.b5827.half 1 true=Geometry.b5862 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5862

theorem bound5794 : BoxMajorant Geometry.b5794 := by
  exact PositiveLeaves.L321.bound

theorem bound5793 : BoxMajorant Geometry.b5793 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5793.Widths)
  · have he : Geometry.b5793.half 0 false=Geometry.b5831 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5831
  · have he : Geometry.b5793.half 0 true=Geometry.b5832 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5832

theorem bound5792 : BoxMajorant Geometry.b5792 := by
  exact PositiveLeaves.L328.bound

theorem bound5791 : BoxMajorant Geometry.b5791 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5791.Widths)
  · have he : Geometry.b5791.half 0 false=Geometry.b5829 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5829
  · have he : Geometry.b5791.half 0 true=Geometry.b5830 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5830

theorem bound5790 : BoxMajorant Geometry.b5790 := by
  exact PositiveLeaves.L331.bound

theorem bound5789 : BoxMajorant Geometry.b5789 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5789.Widths)
  · have he : Geometry.b5789.half 0 false=Geometry.b5827 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5827
  · have he : Geometry.b5789.half 0 true=Geometry.b5828 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5828

theorem bound5788 : BoxMajorant Geometry.b5788 := by
  exact PositiveLeaves.L341.bound

theorem bound5787 : BoxMajorant Geometry.b5787 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5787 Local.C1.center Local.C1.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C1.large_near_majorant hn

theorem bound5732 : BoxMajorant Geometry.b5732 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5732.Widths)
  · have he : Geometry.b5732.half 2 false=Geometry.b5793 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5793
  · have he : Geometry.b5732.half 2 true=Geometry.b5794 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5794

theorem bound5731 : BoxMajorant Geometry.b5731 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5731.Widths)
  · have he : Geometry.b5731.half 2 false=Geometry.b5791 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5791
  · have he : Geometry.b5731.half 2 true=Geometry.b5792 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5792

theorem bound5730 : BoxMajorant Geometry.b5730 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5730.Widths)
  · have he : Geometry.b5730.half 2 false=Geometry.b5789 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5789
  · have he : Geometry.b5730.half 2 true=Geometry.b5790 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5790

theorem bound5729 : BoxMajorant Geometry.b5729 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5729.Widths)
  · have he : Geometry.b5729.half 2 false=Geometry.b5787 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5787
  · have he : Geometry.b5729.half 2 true=Geometry.b5788 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5788

theorem bound5694 : BoxMajorant Geometry.b5694 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5694.Widths)
  · have he : Geometry.b5694.half 1 false=Geometry.b5731 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5731
  · have he : Geometry.b5694.half 1 true=Geometry.b5732 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5732

theorem bound5693 : BoxMajorant Geometry.b5693 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5693.Widths)
  · have he : Geometry.b5693.half 1 false=Geometry.b5729 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5729
  · have he : Geometry.b5693.half 1 true=Geometry.b5730 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5730

theorem bound5660 : BoxMajorant Geometry.b5660 := by
  exact PositiveLeaves.L320.bound

theorem bound5659 : BoxMajorant Geometry.b5659 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5659.Widths)
  · have he : Geometry.b5659.half 0 false=Geometry.b5693 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5693
  · have he : Geometry.b5659.half 0 true=Geometry.b5694 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5694

theorem bound5615 : BoxMajorant Geometry.b5615 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5615.Widths)
  · have he : Geometry.b5615.half 2 false=Geometry.b5659 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5659
  · have he : Geometry.b5615.half 2 true=Geometry.b5660 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5660

end N7.Kernel.Cover
