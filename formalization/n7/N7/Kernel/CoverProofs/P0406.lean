import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.PositiveGroups.G0466
import N7.Kernel.PositiveGroups.G0476
import N7.Kernel.PositiveGroups.G0480
import N7.Kernel.PositiveGroups.G0481
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5542 : BoxMajorant Geometry.b5542 := by
  exact PositiveLeaves.L216.bound

theorem bound5541 : BoxMajorant Geometry.b5541 := by
  exact PositiveLeaves.L217.bound

theorem bound5540 : BoxMajorant Geometry.b5540 := by
  exact PositiveLeaves.L219.bound

theorem bound5539 : BoxMajorant Geometry.b5539 := by
  exact PositiveLeaves.L220.bound

theorem bound5394 : BoxMajorant Geometry.b5394 := by
  exact PositiveLeaves.L215.bound

theorem bound5393 : BoxMajorant Geometry.b5393 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5393.Widths)
  · have he : Geometry.b5393.half 2 false=Geometry.b5541 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5541
  · have he : Geometry.b5393.half 2 true=Geometry.b5542 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5542

theorem bound5392 : BoxMajorant Geometry.b5392 := by
  exact PositiveLeaves.L218.bound

theorem bound5391 : BoxMajorant Geometry.b5391 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5391.Widths)
  · have he : Geometry.b5391.half 2 false=Geometry.b5539 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5539
  · have he : Geometry.b5391.half 2 true=Geometry.b5540 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5540

theorem bound5274 : BoxMajorant Geometry.b5274 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5274.Widths)
  · have he : Geometry.b5274.half 1 false=Geometry.b5393 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5393
  · have he : Geometry.b5274.half 1 true=Geometry.b5394 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5394

theorem bound5273 : BoxMajorant Geometry.b5273 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5273.Widths)
  · have he : Geometry.b5273.half 1 false=Geometry.b5391 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5391
  · have he : Geometry.b5273.half 1 true=Geometry.b5392 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5392

theorem bound5090 : BoxMajorant Geometry.b5090 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5090.Widths)
  · have he : Geometry.b5090.half 0 false=Geometry.b5273 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5273
  · have he : Geometry.b5090.half 0 true=Geometry.b5274 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5274

end N7.Kernel.Cover
