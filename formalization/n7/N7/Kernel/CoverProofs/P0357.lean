import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.PositiveGroups.G0424
import N7.Kernel.PositiveGroups.G0438
import N7.Kernel.PositiveGroups.G0452
import N7.Kernel.PositiveGroups.G0462
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5556 : BoxMajorant Geometry.b5556 := by
  exact PositiveLeaves.L2618.bound

theorem bound5555 : BoxMajorant Geometry.b5555 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5555 2 (by decide +kernel) x hx hd ho).elim

theorem bound5462 : BoxMajorant Geometry.b5462 := by
  exact PositiveLeaves.L2617.bound

theorem bound5461 : BoxMajorant Geometry.b5461 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5461.Widths)
  · have he : Geometry.b5461.half 0 false=Geometry.b5555 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5555
  · have he : Geometry.b5461.half 0 true=Geometry.b5556 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5556

theorem bound5332 : BoxMajorant Geometry.b5332 := by
  exact PositiveLeaves.L2616.bound

theorem bound5331 : BoxMajorant Geometry.b5331 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5331.Widths)
  · have he : Geometry.b5331.half 2 false=Geometry.b5461 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5461
  · have he : Geometry.b5331.half 2 true=Geometry.b5462 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5462

theorem bound5150 : BoxMajorant Geometry.b5150 := by
  exact PositiveLeaves.L2615.bound

theorem bound5149 : BoxMajorant Geometry.b5149 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5149.Widths)
  · have he : Geometry.b5149.half 1 false=Geometry.b5331 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5331
  · have he : Geometry.b5149.half 1 true=Geometry.b5332 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5332

theorem bound4792 : BoxMajorant Geometry.b4792 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4792.Widths)
  · have he : Geometry.b4792.half 0 false=Geometry.b5149 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5149
  · have he : Geometry.b4792.half 0 true=Geometry.b5150 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5150

end N7.Kernel.Cover
