import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.PositiveGroups.G0387
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5564 : BoxMajorant Geometry.b5564 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5564 0 (by decide +kernel) x hx hd ho).elim

theorem bound5563 : BoxMajorant Geometry.b5563 := by
  exact PositiveLeaves.L1302.bound

theorem bound5490 : BoxMajorant Geometry.b5490 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5490.Widths)
  · have he : Geometry.b5490.half 0 false=Geometry.b5563 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5563
  · have he : Geometry.b5490.half 0 true=Geometry.b5564 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5564

theorem bound5489 : BoxMajorant Geometry.b5489 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5489 2 (by decide +kernel) x hx hd ho).elim

theorem bound5360 : BoxMajorant Geometry.b5360 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5360.Widths)
  · have he : Geometry.b5360.half 2 false=Geometry.b5489 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5489
  · have he : Geometry.b5360.half 2 true=Geometry.b5490 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5490

end N7.Kernel.Cover
