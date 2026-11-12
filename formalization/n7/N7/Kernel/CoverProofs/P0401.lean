import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.PositiveGroups.G0446
import N7.Kernel.PositiveGroups.G0465
import N7.Kernel.PositiveGroups.G0466
import N7.Kernel.PositiveGroups.G0473
import N7.Kernel.PositiveGroups.G0474
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5550 : BoxMajorant Geometry.b5550 := by
  exact PositiveLeaves.L198.bound

theorem bound5549 : BoxMajorant Geometry.b5549 := by
  exact PositiveLeaves.L199.bound

theorem bound5548 : BoxMajorant Geometry.b5548 := by
  exact PositiveLeaves.L200.bound

theorem bound5547 : BoxMajorant Geometry.b5547 := by
  exact PositiveLeaves.L201.bound

theorem bound5546 : BoxMajorant Geometry.b5546 := by
  exact PositiveLeaves.L202.bound

theorem bound5545 : BoxMajorant Geometry.b5545 := by
  exact PositiveLeaves.L203.bound

theorem bound5544 : BoxMajorant Geometry.b5544 := by
  exact PositiveLeaves.L204.bound

theorem bound5543 : BoxMajorant Geometry.b5543 := by
  exact PositiveLeaves.L205.bound

theorem bound5398 : BoxMajorant Geometry.b5398 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5398.Widths)
  · have he : Geometry.b5398.half 2 false=Geometry.b5549 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5549
  · have he : Geometry.b5398.half 2 true=Geometry.b5550 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5550

theorem bound5397 : BoxMajorant Geometry.b5397 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5397.Widths)
  · have he : Geometry.b5397.half 2 false=Geometry.b5547 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5547
  · have he : Geometry.b5397.half 2 true=Geometry.b5548 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5548

theorem bound5396 : BoxMajorant Geometry.b5396 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5396.Widths)
  · have he : Geometry.b5396.half 2 false=Geometry.b5545 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5545
  · have he : Geometry.b5396.half 2 true=Geometry.b5546 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5546

theorem bound5395 : BoxMajorant Geometry.b5395 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5395.Widths)
  · have he : Geometry.b5395.half 2 false=Geometry.b5543 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5543
  · have he : Geometry.b5395.half 2 true=Geometry.b5544 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5544

theorem bound5276 : BoxMajorant Geometry.b5276 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5276.Widths)
  · have he : Geometry.b5276.half 1 false=Geometry.b5397 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5397
  · have he : Geometry.b5276.half 1 true=Geometry.b5398 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5398

theorem bound5275 : BoxMajorant Geometry.b5275 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5275.Widths)
  · have he : Geometry.b5275.half 1 false=Geometry.b5395 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5395
  · have he : Geometry.b5275.half 1 true=Geometry.b5396 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5396

theorem bound5096 : BoxMajorant Geometry.b5096 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5096.Widths)
  · have he : Geometry.b5096.half 0 false=Geometry.b5275 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5275
  · have he : Geometry.b5096.half 0 true=Geometry.b5276 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5276

theorem bound5095 : BoxMajorant Geometry.b5095 := by
  exact PositiveLeaves.L206.bound

theorem bound4709 : BoxMajorant Geometry.b4709 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4709.Widths)
  · have he : Geometry.b4709.half 2 false=Geometry.b5095 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5095
  · have he : Geometry.b4709.half 2 true=Geometry.b5096 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5096

end N7.Kernel.Cover
