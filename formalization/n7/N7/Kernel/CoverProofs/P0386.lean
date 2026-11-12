import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.PositiveGroups.G0443
import N7.Kernel.PositiveGroups.G0457
import N7.Kernel.PositiveGroups.G0458
import N7.Kernel.PositiveGroups.G0463
import N7.Kernel.PositiveGroups.G0464
import N7.Kernel.PositiveGroups.G0472
import N7.Kernel.PositiveGroups.G0473
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5886 : BoxMajorant Geometry.b5886 := by
  exact PositiveLeaves.L1014.bound

theorem bound5885 : BoxMajorant Geometry.b5885 := by
  exact PositiveLeaves.L1015.bound

theorem bound5848 : BoxMajorant Geometry.b5848 := by
  exact PositiveLeaves.L1013.bound

theorem bound5847 : BoxMajorant Geometry.b5847 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5847.Widths)
  · have he : Geometry.b5847.half 2 false=Geometry.b5885 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5885
  · have he : Geometry.b5847.half 2 true=Geometry.b5886 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5886

theorem bound5816 : BoxMajorant Geometry.b5816 := by
  exact PositiveLeaves.L1012.bound

theorem bound5815 : BoxMajorant Geometry.b5815 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5815.Widths)
  · have he : Geometry.b5815.half 1 false=Geometry.b5847 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5847
  · have he : Geometry.b5815.half 1 true=Geometry.b5848 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5848

theorem bound5760 : BoxMajorant Geometry.b5760 := by
  exact PositiveLeaves.L1009.bound

theorem bound5759 : BoxMajorant Geometry.b5759 := by
  exact PositiveLeaves.L1010.bound

theorem bound5758 : BoxMajorant Geometry.b5758 := by
  exact PositiveLeaves.L1011.bound

theorem bound5757 : BoxMajorant Geometry.b5757 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5757.Widths)
  · have he : Geometry.b5757.half 0 false=Geometry.b5815 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5815
  · have he : Geometry.b5757.half 0 true=Geometry.b5816 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5816

theorem bound5710 : BoxMajorant Geometry.b5710 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5710.Widths)
  · have he : Geometry.b5710.half 2 false=Geometry.b5759 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5759
  · have he : Geometry.b5710.half 2 true=Geometry.b5760 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5760

theorem bound5709 : BoxMajorant Geometry.b5709 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5709.Widths)
  · have he : Geometry.b5709.half 2 false=Geometry.b5757 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5757
  · have he : Geometry.b5709.half 2 true=Geometry.b5758 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5758

theorem bound5680 : BoxMajorant Geometry.b5680 := by
  exact PositiveLeaves.L1008.bound

theorem bound5679 : BoxMajorant Geometry.b5679 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5679.Widths)
  · have he : Geometry.b5679.half 1 false=Geometry.b5709 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5709
  · have he : Geometry.b5679.half 1 true=Geometry.b5710 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5710

theorem bound5633 : BoxMajorant Geometry.b5633 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5633.Widths)
  · have he : Geometry.b5633.half 0 false=Geometry.b5679 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5679
  · have he : Geometry.b5633.half 0 true=Geometry.b5680 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5680

end N7.Kernel.Cover
