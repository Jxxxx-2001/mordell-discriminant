import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverProofs.P0412
import N7.Kernel.CoverProofs.P0413
import N7.Kernel.CoverProofs.P0414
import N7.Kernel.CoverProofs.P0415
import N7.Kernel.CoverProofs.P0416
import N7.Kernel.CoverProofs.P0417
import N7.Kernel.CoverProofs.P0418
import N7.Kernel.PositiveGroups.G0449
import N7.Kernel.PositiveGroups.G0467
import N7.Kernel.PositiveGroups.G0476
import N7.Kernel.PositiveGroups.G0477
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5613 : BoxMajorant Geometry.b5613 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5613 0 (by decide +kernel) x hx hd ho).elim

theorem bound5588 : BoxMajorant Geometry.b5588 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5588 0 (by decide +kernel) x hx hd ho).elim

theorem bound5586 : BoxMajorant Geometry.b5586 := by
  exact PositiveLeaves.L294.bound

theorem bound5584 : BoxMajorant Geometry.b5584 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5584.Widths)
  · have he : Geometry.b5584.half 1 false=Geometry.b5617 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5617
  · have he : Geometry.b5584.half 1 true=Geometry.b5618 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5618

theorem bound5583 : BoxMajorant Geometry.b5583 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5583.Widths)
  · have he : Geometry.b5583.half 1 false=Geometry.b5615 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5615
  · have he : Geometry.b5583.half 1 true=Geometry.b5616 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5616

theorem bound5582 : BoxMajorant Geometry.b5582 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5582 0 (by decide +kernel) x hx hd ho).elim

theorem bound5581 : BoxMajorant Geometry.b5581 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5581.Widths)
  · have he : Geometry.b5581.half 1 false=Geometry.b5613 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5613
  · have he : Geometry.b5581.half 1 true=Geometry.b5614 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5614

theorem bound5528 : BoxMajorant Geometry.b5528 := by
  exact PositiveLeaves.L288.bound

theorem bound5527 : BoxMajorant Geometry.b5527 := by
  exact PositiveLeaves.L289.bound

theorem bound5526 : BoxMajorant Geometry.b5526 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5526.Widths)
  · have he : Geometry.b5526.half 0 false=Geometry.b5587 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5587
  · have he : Geometry.b5526.half 0 true=Geometry.b5588 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5588

theorem bound5525 : BoxMajorant Geometry.b5525 := by
  exact PositiveLeaves.L293.bound

theorem bound5524 : BoxMajorant Geometry.b5524 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5524.Widths)
  · have he : Geometry.b5524.half 0 false=Geometry.b5585 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5585
  · have he : Geometry.b5524.half 0 true=Geometry.b5586 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5586

theorem bound5523 : BoxMajorant Geometry.b5523 := by
  exact PositiveLeaves.L298.bound

theorem bound5522 : BoxMajorant Geometry.b5522 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5522.Widths)
  · have he : Geometry.b5522.half 0 false=Geometry.b5583 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5583
  · have he : Geometry.b5522.half 0 true=Geometry.b5584 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5584

theorem bound5521 : BoxMajorant Geometry.b5521 := by
  exact PositiveLeaves.L343.bound

theorem bound5520 : BoxMajorant Geometry.b5520 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5520.Widths)
  · have he : Geometry.b5520.half 0 false=Geometry.b5581 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5581
  · have he : Geometry.b5520.half 0 true=Geometry.b5582 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5582

theorem bound5519 : BoxMajorant Geometry.b5519 := by
  exact PositiveLeaves.L354.bound

theorem bound5384 : BoxMajorant Geometry.b5384 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5384.Widths)
  · have he : Geometry.b5384.half 2 false=Geometry.b5527 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5527
  · have he : Geometry.b5384.half 2 true=Geometry.b5528 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5528

theorem bound5383 : BoxMajorant Geometry.b5383 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5383.Widths)
  · have he : Geometry.b5383.half 2 false=Geometry.b5525 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5525
  · have he : Geometry.b5383.half 2 true=Geometry.b5526 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5526

theorem bound5382 : BoxMajorant Geometry.b5382 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5382.Widths)
  · have he : Geometry.b5382.half 2 false=Geometry.b5523 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5523
  · have he : Geometry.b5382.half 2 true=Geometry.b5524 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5524

theorem bound5381 : BoxMajorant Geometry.b5381 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5381.Widths)
  · have he : Geometry.b5381.half 2 false=Geometry.b5521 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5521
  · have he : Geometry.b5381.half 2 true=Geometry.b5522 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5522

theorem bound5380 : BoxMajorant Geometry.b5380 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5380.Widths)
  · have he : Geometry.b5380.half 2 false=Geometry.b5519 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5519
  · have he : Geometry.b5380.half 2 true=Geometry.b5520 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5520

theorem bound5379 : BoxMajorant Geometry.b5379 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5379 0 (by decide +kernel) x hx hd ho).elim

theorem bound5268 : BoxMajorant Geometry.b5268 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5268.Widths)
  · have he : Geometry.b5268.half 1 false=Geometry.b5383 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5383
  · have he : Geometry.b5268.half 1 true=Geometry.b5384 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5384

theorem bound5267 : BoxMajorant Geometry.b5267 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5267.Widths)
  · have he : Geometry.b5267.half 1 false=Geometry.b5381 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5381
  · have he : Geometry.b5267.half 1 true=Geometry.b5382 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5382

theorem bound5266 : BoxMajorant Geometry.b5266 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5266 0 (by decide +kernel) x hx hd ho).elim

theorem bound5265 : BoxMajorant Geometry.b5265 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5265.Widths)
  · have he : Geometry.b5265.half 1 false=Geometry.b5379 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5379
  · have he : Geometry.b5265.half 1 true=Geometry.b5380 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5380

theorem bound5068 : BoxMajorant Geometry.b5068 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5068.Widths)
  · have he : Geometry.b5068.half 0 false=Geometry.b5267 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5267
  · have he : Geometry.b5068.half 0 true=Geometry.b5268 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5268

theorem bound5067 : BoxMajorant Geometry.b5067 := by
  exact PositiveLeaves.L344.bound

theorem bound5066 : BoxMajorant Geometry.b5066 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5066.Widths)
  · have he : Geometry.b5066.half 0 false=Geometry.b5265 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5265
  · have he : Geometry.b5066.half 0 true=Geometry.b5266 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5266

theorem bound5065 : BoxMajorant Geometry.b5065 := by
  exact PositiveLeaves.L356.bound

theorem bound4688 : BoxMajorant Geometry.b4688 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4688.Widths)
  · have he : Geometry.b4688.half 2 false=Geometry.b5067 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5067
  · have he : Geometry.b4688.half 2 true=Geometry.b5068 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5068

theorem bound4687 : BoxMajorant Geometry.b4687 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4687.Widths)
  · have he : Geometry.b4687.half 2 false=Geometry.b5065 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5065
  · have he : Geometry.b4687.half 2 true=Geometry.b5066 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5066

theorem bound4418 : BoxMajorant Geometry.b4418 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4418.Widths)
  · have he : Geometry.b4418.half 1 false=Geometry.b4687 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4687
  · have he : Geometry.b4418.half 1 true=Geometry.b4688 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4688

end N7.Kernel.Cover
