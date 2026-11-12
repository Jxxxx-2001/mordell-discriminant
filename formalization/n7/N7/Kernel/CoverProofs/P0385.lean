import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.LocalBridge
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.Local.C0LargeMajorant
import N7.Kernel.PositiveGroups.G0429
import N7.Kernel.PositiveGroups.G0457
import N7.Kernel.PositiveGroups.G0464
import N7.Kernel.PositiveGroups.G0472
import N7.Kernel.PositiveGroups.G0473
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5884 : BoxMajorant Geometry.b5884 := by
  exact PositiveLeaves.L1020.bound

theorem bound5883 : BoxMajorant Geometry.b5883 := by
  exact PositiveLeaves.L1021.bound

theorem bound5846 : BoxMajorant Geometry.b5846 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5846.Widths)
  · have he : Geometry.b5846.half 2 false=Geometry.b5883 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5883
  · have he : Geometry.b5846.half 2 true=Geometry.b5884 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5884

theorem bound5845 : BoxMajorant Geometry.b5845 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5845 Local.C0.center Local.C0.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C0.large_near_majorant hn hd.1

theorem bound5814 : BoxMajorant Geometry.b5814 := by
  exact PositiveLeaves.L1019.bound

theorem bound5813 : BoxMajorant Geometry.b5813 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5813.Widths)
  · have he : Geometry.b5813.half 1 false=Geometry.b5845 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5845
  · have he : Geometry.b5813.half 1 true=Geometry.b5846 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5846

theorem bound5756 : BoxMajorant Geometry.b5756 := by
  exact PositiveLeaves.L1018.bound

theorem bound5755 : BoxMajorant Geometry.b5755 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5755.Widths)
  · have he : Geometry.b5755.half 0 false=Geometry.b5813 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5813
  · have he : Geometry.b5755.half 0 true=Geometry.b5814 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5814

theorem bound5754 : BoxMajorant Geometry.b5754 := by
  exact PositiveLeaves.L1023.bound

theorem bound5753 : BoxMajorant Geometry.b5753 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5753 Local.C0.center Local.C0.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C0.large_near_majorant hn hd.1

theorem bound5708 : BoxMajorant Geometry.b5708 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5708.Widths)
  · have he : Geometry.b5708.half 2 false=Geometry.b5755 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5755
  · have he : Geometry.b5708.half 2 true=Geometry.b5756 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5756

theorem bound5707 : BoxMajorant Geometry.b5707 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5707.Widths)
  · have he : Geometry.b5707.half 2 false=Geometry.b5753 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5753
  · have he : Geometry.b5707.half 2 true=Geometry.b5754 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5754

theorem bound5678 : BoxMajorant Geometry.b5678 := by
  exact PositiveLeaves.L1017.bound

theorem bound5677 : BoxMajorant Geometry.b5677 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5677.Widths)
  · have he : Geometry.b5677.half 1 false=Geometry.b5707 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5707
  · have he : Geometry.b5677.half 1 true=Geometry.b5708 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5708

theorem bound5631 : BoxMajorant Geometry.b5631 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5631.Widths)
  · have he : Geometry.b5631.half 0 false=Geometry.b5677 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5677
  · have he : Geometry.b5631.half 0 true=Geometry.b5678 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5678

end N7.Kernel.Cover
