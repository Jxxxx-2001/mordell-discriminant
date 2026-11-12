import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverProofs.P0381
import N7.Kernel.CoverProofs.P0382
import N7.Kernel.CoverProofs.P0383
import N7.Kernel.CoverProofs.P0384
import N7.Kernel.PositiveGroups.G0386
import N7.Kernel.PositiveGroups.G0410
import N7.Kernel.PositiveGroups.G0428
import N7.Kernel.PositiveGroups.G0442
import N7.Kernel.PositiveGroups.G0456
import N7.Kernel.PositiveGroups.G0457
import N7.Kernel.PositiveGroups.G0462
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5837 : BoxMajorant Geometry.b5837 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5837 2 (by decide +kernel) x hx hd ho).elim

theorem bound5812 : BoxMajorant Geometry.b5812 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5812 0 (by decide +kernel) x hx hd ho).elim

theorem bound5809 : BoxMajorant Geometry.b5809 := by
  exact PositiveLeaves.L1277.bound

theorem bound5807 : BoxMajorant Geometry.b5807 := by
  exact PositiveLeaves.L1285.bound

theorem bound5806 : BoxMajorant Geometry.b5806 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5806.Widths)
  · have he : Geometry.b5806.half 1 false=Geometry.b5837 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5837
  · have he : Geometry.b5806.half 1 true=Geometry.b5838 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5838

theorem bound5805 : BoxMajorant Geometry.b5805 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5805 2 (by decide +kernel) x hx hd ho).elim

theorem bound5752 : BoxMajorant Geometry.b5752 := by
  exact PositiveLeaves.L1267.bound

theorem bound5751 : BoxMajorant Geometry.b5751 := by
  exact PositiveLeaves.L1268.bound

theorem bound5750 : BoxMajorant Geometry.b5750 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5750.Widths)
  · have he : Geometry.b5750.half 0 false=Geometry.b5811 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5811
  · have he : Geometry.b5750.half 0 true=Geometry.b5812 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5812

theorem bound5749 : BoxMajorant Geometry.b5749 := by
  exact PositiveLeaves.L1273.bound

theorem bound5748 : BoxMajorant Geometry.b5748 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5748.Widths)
  · have he : Geometry.b5748.half 0 false=Geometry.b5809 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5809
  · have he : Geometry.b5748.half 0 true=Geometry.b5810 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5810

theorem bound5747 : BoxMajorant Geometry.b5747 := by
  exact PositiveLeaves.L1278.bound

theorem bound5746 : BoxMajorant Geometry.b5746 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5746.Widths)
  · have he : Geometry.b5746.half 0 false=Geometry.b5807 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5807
  · have he : Geometry.b5746.half 0 true=Geometry.b5808 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5808

theorem bound5745 : BoxMajorant Geometry.b5745 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5745.Widths)
  · have he : Geometry.b5745.half 0 false=Geometry.b5805 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5805
  · have he : Geometry.b5745.half 0 true=Geometry.b5806 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5806

theorem bound5706 : BoxMajorant Geometry.b5706 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5706.Widths)
  · have he : Geometry.b5706.half 2 false=Geometry.b5751 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5751
  · have he : Geometry.b5706.half 2 true=Geometry.b5752 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5752

theorem bound5705 : BoxMajorant Geometry.b5705 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5705.Widths)
  · have he : Geometry.b5705.half 2 false=Geometry.b5749 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5749
  · have he : Geometry.b5705.half 2 true=Geometry.b5750 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5750

theorem bound5704 : BoxMajorant Geometry.b5704 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5704.Widths)
  · have he : Geometry.b5704.half 2 false=Geometry.b5747 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5747
  · have he : Geometry.b5704.half 2 true=Geometry.b5748 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5748

theorem bound5703 : BoxMajorant Geometry.b5703 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5703.Widths)
  · have he : Geometry.b5703.half 2 false=Geometry.b5745 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5745
  · have he : Geometry.b5703.half 2 true=Geometry.b5746 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5746

theorem bound5676 : BoxMajorant Geometry.b5676 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5676.Widths)
  · have he : Geometry.b5676.half 1 false=Geometry.b5705 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5705
  · have he : Geometry.b5676.half 1 true=Geometry.b5706 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5706

theorem bound5675 : BoxMajorant Geometry.b5675 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5675.Widths)
  · have he : Geometry.b5675.half 1 false=Geometry.b5703 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5703
  · have he : Geometry.b5675.half 1 true=Geometry.b5704 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5704

theorem bound5674 : BoxMajorant Geometry.b5674 := by
  exact PositiveLeaves.L1295.bound

theorem bound5673 : BoxMajorant Geometry.b5673 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5673 2 (by decide +kernel) x hx hd ho).elim

theorem bound5630 : BoxMajorant Geometry.b5630 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5630.Widths)
  · have he : Geometry.b5630.half 0 false=Geometry.b5675 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5675
  · have he : Geometry.b5630.half 0 true=Geometry.b5676 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5676

theorem bound5629 : BoxMajorant Geometry.b5629 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5629.Widths)
  · have he : Geometry.b5629.half 0 false=Geometry.b5673 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5673
  · have he : Geometry.b5629.half 0 true=Geometry.b5674 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5674

theorem bound5596 : BoxMajorant Geometry.b5596 := by
  exact PositiveLeaves.L1266.bound

theorem bound5595 : BoxMajorant Geometry.b5595 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5595.Widths)
  · have he : Geometry.b5595.half 2 false=Geometry.b5629 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5629
  · have he : Geometry.b5595.half 2 true=Geometry.b5630 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5630

theorem bound5568 : BoxMajorant Geometry.b5568 := by
  exact PositiveLeaves.L1265.bound

theorem bound5567 : BoxMajorant Geometry.b5567 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5567.Widths)
  · have he : Geometry.b5567.half 1 false=Geometry.b5595 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5595
  · have he : Geometry.b5567.half 1 true=Geometry.b5596 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5596

theorem bound5566 : BoxMajorant Geometry.b5566 := by
  exact PositiveLeaves.L1297.bound

theorem bound5565 : BoxMajorant Geometry.b5565 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5565 2 (by decide +kernel) x hx hd ho).elim

theorem bound5492 : BoxMajorant Geometry.b5492 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5492.Widths)
  · have he : Geometry.b5492.half 0 false=Geometry.b5567 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5567
  · have he : Geometry.b5492.half 0 true=Geometry.b5568 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5568

theorem bound5491 : BoxMajorant Geometry.b5491 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5491.Widths)
  · have he : Geometry.b5491.half 0 false=Geometry.b5565 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5565
  · have he : Geometry.b5491.half 0 true=Geometry.b5566 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5566

theorem bound5362 : BoxMajorant Geometry.b5362 := by
  exact PositiveLeaves.L1264.bound

theorem bound5361 : BoxMajorant Geometry.b5361 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5361.Widths)
  · have he : Geometry.b5361.half 2 false=Geometry.b5491 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5491
  · have he : Geometry.b5361.half 2 true=Geometry.b5492 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5492

theorem bound5253 : BoxMajorant Geometry.b5253 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5253.Widths)
  · have he : Geometry.b5253.half 1 false=Geometry.b5361 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5361
  · have he : Geometry.b5253.half 1 true=Geometry.b5362 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5362

end N7.Kernel.Cover
