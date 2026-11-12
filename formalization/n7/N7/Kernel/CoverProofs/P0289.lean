import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.PositiveGroups.G0354
import N7.Kernel.PositiveGroups.G0386
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5594 : BoxMajorant Geometry.b5594 := by
  exact PositiveLeaves.L1307.bound

theorem bound5593 : BoxMajorant Geometry.b5593 := by
  exact PositiveLeaves.L1308.bound

theorem bound5562 : BoxMajorant Geometry.b5562 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5562.Widths)
  · have he : Geometry.b5562.half 1 false=Geometry.b5593 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5593
  · have he : Geometry.b5562.half 1 true=Geometry.b5594 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5594

theorem bound5561 : BoxMajorant Geometry.b5561 := by
  exact PositiveLeaves.L1309.bound

theorem bound5488 : BoxMajorant Geometry.b5488 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5488.Widths)
  · have he : Geometry.b5488.half 0 false=Geometry.b5561 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5561
  · have he : Geometry.b5488.half 0 true=Geometry.b5562 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5562

theorem bound5487 : BoxMajorant Geometry.b5487 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5487 2 (by decide +kernel) x hx hd ho).elim

theorem bound5357 : BoxMajorant Geometry.b5357 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5357.Widths)
  · have he : Geometry.b5357.half 2 false=Geometry.b5487 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5487
  · have he : Geometry.b5357.half 2 true=Geometry.b5488 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5488

end N7.Kernel.Cover
