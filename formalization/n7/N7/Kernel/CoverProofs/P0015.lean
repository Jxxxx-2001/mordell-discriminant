import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0004
import N7.Kernel.CoverGeometry.G0006
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverProofs.P0105
import N7.Kernel.CoverProofs.P0106
import N7.Kernel.CoverProofs.P0107
import N7.Kernel.CoverProofs.P0108
import N7.Kernel.CoverProofs.P0109
import N7.Kernel.CoverProofs.P0110
import N7.Kernel.CoverProofs.P0111
import N7.Kernel.CoverProofs.P0112
import N7.Kernel.CoverProofs.P0113
import N7.Kernel.CoverProofs.P0114
import N7.Kernel.CoverProofs.P0115
import N7.Kernel.PositiveGroups.G0002
import N7.Kernel.PositiveGroups.G0008
import N7.Kernel.PositiveGroups.G0015
import N7.Kernel.PositiveGroups.G0030
import N7.Kernel.PositiveGroups.G0031
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound892 : BoxMajorant Geometry.b892 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b892 0 (by decide +kernel) x hx hd ho).elim

theorem bound886 : BoxMajorant Geometry.b886 := by
  exact PositiveLeaves.L1088.bound

theorem bound885 : BoxMajorant Geometry.b885 := by
  exact PositiveLeaves.L1089.bound

theorem bound884 : BoxMajorant Geometry.b884 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b884 0 (by decide +kernel) x hx hd ho).elim

theorem bound882 : BoxMajorant Geometry.b882 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b882 0 (by decide +kernel) x hx hd ho).elim

theorem bound618 : BoxMajorant Geometry.b618 := by
  exact PositiveLeaves.L1030.bound

theorem bound616 : BoxMajorant Geometry.b616 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b616 1 (by decide +kernel) x hx hd ho).elim

theorem bound614 : BoxMajorant Geometry.b614 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b614 1 (by decide +kernel) x hx hd ho).elim

theorem bound611 : BoxMajorant Geometry.b611 := by
  exact PositiveLeaves.L1065.bound

theorem bound610 : BoxMajorant Geometry.b610 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b610.Widths)
  · have he : Geometry.b610.half 0 false=Geometry.b891 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound891
  · have he : Geometry.b610.half 0 true=Geometry.b892 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound892

theorem bound609 : BoxMajorant Geometry.b609 := by
  exact PositiveLeaves.L1070.bound

theorem bound608 : BoxMajorant Geometry.b608 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b608.Widths)
  · have he : Geometry.b608.half 0 false=Geometry.b889 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound889
  · have he : Geometry.b608.half 0 true=Geometry.b890 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound890

theorem bound607 : BoxMajorant Geometry.b607 := by
  exact PositiveLeaves.L1079.bound

theorem bound606 : BoxMajorant Geometry.b606 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b606.Widths)
  · have he : Geometry.b606.half 0 false=Geometry.b887 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound887
  · have he : Geometry.b606.half 0 true=Geometry.b888 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound888

theorem bound605 : BoxMajorant Geometry.b605 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b605.Widths)
  · have he : Geometry.b605.half 0 false=Geometry.b885 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound885
  · have he : Geometry.b605.half 0 true=Geometry.b886 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound886

theorem bound604 : BoxMajorant Geometry.b604 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b604.Widths)
  · have he : Geometry.b604.half 0 false=Geometry.b883 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound883
  · have he : Geometry.b604.half 0 true=Geometry.b884 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound884

theorem bound603 : BoxMajorant Geometry.b603 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b603.Widths)
  · have he : Geometry.b603.half 0 false=Geometry.b881 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound881
  · have he : Geometry.b603.half 0 true=Geometry.b882 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound882

theorem bound398 : BoxMajorant Geometry.b398 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b398.Widths)
  · have he : Geometry.b398.half 2 false=Geometry.b617 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound617
  · have he : Geometry.b398.half 2 true=Geometry.b618 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound618

theorem bound397 : BoxMajorant Geometry.b397 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b397.Widths)
  · have he : Geometry.b397.half 2 false=Geometry.b615 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound615
  · have he : Geometry.b397.half 2 true=Geometry.b616 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound616

theorem bound396 : BoxMajorant Geometry.b396 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b396.Widths)
  · have he : Geometry.b396.half 2 false=Geometry.b613 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound613
  · have he : Geometry.b396.half 2 true=Geometry.b614 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound614

theorem bound395 : BoxMajorant Geometry.b395 := by
  exact PositiveLeaves.L1062.bound

theorem bound394 : BoxMajorant Geometry.b394 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b394.Widths)
  · have he : Geometry.b394.half 2 false=Geometry.b611 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound611
  · have he : Geometry.b394.half 2 true=Geometry.b612 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound612

theorem bound393 : BoxMajorant Geometry.b393 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b393.Widths)
  · have he : Geometry.b393.half 2 false=Geometry.b609 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound609
  · have he : Geometry.b393.half 2 true=Geometry.b610 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound610

theorem bound392 : BoxMajorant Geometry.b392 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b392.Widths)
  · have he : Geometry.b392.half 2 false=Geometry.b607 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound607
  · have he : Geometry.b392.half 2 true=Geometry.b608 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound608

theorem bound391 : BoxMajorant Geometry.b391 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b391.Widths)
  · have he : Geometry.b391.half 2 false=Geometry.b605 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound605
  · have he : Geometry.b391.half 2 true=Geometry.b606 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound606

theorem bound390 : BoxMajorant Geometry.b390 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b390.Widths)
  · have he : Geometry.b390.half 2 false=Geometry.b603 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound603
  · have he : Geometry.b390.half 2 true=Geometry.b604 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound604

theorem bound389 : BoxMajorant Geometry.b389 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b389 0 (by decide +kernel) x hx hd ho).elim

theorem bound256 : BoxMajorant Geometry.b256 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b256.Widths)
  · have he : Geometry.b256.half 1 false=Geometry.b397 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound397
  · have he : Geometry.b256.half 1 true=Geometry.b398 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound398

theorem bound255 : BoxMajorant Geometry.b255 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b255.Widths)
  · have he : Geometry.b255.half 1 false=Geometry.b395 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound395
  · have he : Geometry.b255.half 1 true=Geometry.b396 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound396

theorem bound254 : BoxMajorant Geometry.b254 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b254.Widths)
  · have he : Geometry.b254.half 1 false=Geometry.b393 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound393
  · have he : Geometry.b254.half 1 true=Geometry.b394 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound394

theorem bound253 : BoxMajorant Geometry.b253 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b253.Widths)
  · have he : Geometry.b253.half 1 false=Geometry.b391 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound391
  · have he : Geometry.b253.half 1 true=Geometry.b392 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound392

theorem bound252 : BoxMajorant Geometry.b252 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b252 0 (by decide +kernel) x hx hd ho).elim

theorem bound251 : BoxMajorant Geometry.b251 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b251.Widths)
  · have he : Geometry.b251.half 1 false=Geometry.b389 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound389
  · have he : Geometry.b251.half 1 true=Geometry.b390 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound390

theorem bound156 : BoxMajorant Geometry.b156 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b156.Widths)
  · have he : Geometry.b156.half 0 false=Geometry.b255 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound255
  · have he : Geometry.b156.half 0 true=Geometry.b256 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound256

theorem bound155 : BoxMajorant Geometry.b155 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b155.Widths)
  · have he : Geometry.b155.half 0 false=Geometry.b253 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound253
  · have he : Geometry.b155.half 0 true=Geometry.b254 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound254

theorem bound154 : BoxMajorant Geometry.b154 := by
  exact PositiveLeaves.L1090.bound

theorem bound153 : BoxMajorant Geometry.b153 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b153.Widths)
  · have he : Geometry.b153.half 0 false=Geometry.b251 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound251
  · have he : Geometry.b153.half 0 true=Geometry.b252 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound252

theorem bound90 : BoxMajorant Geometry.b90 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b90.Widths)
  · have he : Geometry.b90.half 2 false=Geometry.b155 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound155
  · have he : Geometry.b90.half 2 true=Geometry.b156 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound156

theorem bound89 : BoxMajorant Geometry.b89 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b89.Widths)
  · have he : Geometry.b89.half 2 false=Geometry.b153 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound153
  · have he : Geometry.b89.half 2 true=Geometry.b154 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound154

theorem bound48 : BoxMajorant Geometry.b48 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b48.Widths)
  · have he : Geometry.b48.half 1 false=Geometry.b89 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound89
  · have he : Geometry.b48.half 1 true=Geometry.b90 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound90

end N7.Kernel.Cover
