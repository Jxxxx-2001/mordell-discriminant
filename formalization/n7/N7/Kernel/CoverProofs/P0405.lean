import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.PositiveGroups.G0474
import N7.Kernel.PositiveGroups.G0475
import N7.Kernel.PositiveGroups.G0476
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5538 : BoxMajorant Geometry.b5538 := by
  exact PositiveLeaves.L222.bound

theorem bound5537 : BoxMajorant Geometry.b5537 := by
  exact PositiveLeaves.L223.bound

theorem bound5536 : BoxMajorant Geometry.b5536 := by
  exact PositiveLeaves.L224.bound

theorem bound5535 : BoxMajorant Geometry.b5535 := by
  exact PositiveLeaves.L225.bound

theorem bound5534 : BoxMajorant Geometry.b5534 := by
  exact PositiveLeaves.L226.bound

theorem bound5533 : BoxMajorant Geometry.b5533 := by
  exact PositiveLeaves.L227.bound

theorem bound5532 : BoxMajorant Geometry.b5532 := by
  exact PositiveLeaves.L228.bound

theorem bound5531 : BoxMajorant Geometry.b5531 := by
  exact PositiveLeaves.L229.bound

theorem bound5390 : BoxMajorant Geometry.b5390 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5390.Widths)
  · have he : Geometry.b5390.half 2 false=Geometry.b5537 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5537
  · have he : Geometry.b5390.half 2 true=Geometry.b5538 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5538

theorem bound5389 : BoxMajorant Geometry.b5389 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5389.Widths)
  · have he : Geometry.b5389.half 2 false=Geometry.b5535 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5535
  · have he : Geometry.b5389.half 2 true=Geometry.b5536 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5536

theorem bound5388 : BoxMajorant Geometry.b5388 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5388.Widths)
  · have he : Geometry.b5388.half 2 false=Geometry.b5533 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5533
  · have he : Geometry.b5388.half 2 true=Geometry.b5534 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5534

theorem bound5387 : BoxMajorant Geometry.b5387 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5387.Widths)
  · have he : Geometry.b5387.half 2 false=Geometry.b5531 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5531
  · have he : Geometry.b5387.half 2 true=Geometry.b5532 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5532

theorem bound5272 : BoxMajorant Geometry.b5272 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5272.Widths)
  · have he : Geometry.b5272.half 1 false=Geometry.b5389 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5389
  · have he : Geometry.b5272.half 1 true=Geometry.b5390 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5390

theorem bound5271 : BoxMajorant Geometry.b5271 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5271.Widths)
  · have he : Geometry.b5271.half 1 false=Geometry.b5387 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5387
  · have he : Geometry.b5271.half 1 true=Geometry.b5388 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5388

theorem bound5088 : BoxMajorant Geometry.b5088 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5088.Widths)
  · have he : Geometry.b5088.half 0 false=Geometry.b5271 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5271
  · have he : Geometry.b5088.half 0 true=Geometry.b5272 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5272

end N7.Kernel.Cover
