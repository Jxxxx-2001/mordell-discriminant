import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.PositiveGroups.G0111
import N7.Kernel.PositiveGroups.G0150
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2122 : BoxMajorant Geometry.b2122 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2122 0 (by decide +kernel) x hx hd ho).elim

theorem bound2121 : BoxMajorant Geometry.b2121 := by
  exact PositiveLeaves.L2646.bound

theorem bound1474 : BoxMajorant Geometry.b1474 := by
  exact PositiveLeaves.L2644.bound

theorem bound1473 : BoxMajorant Geometry.b1473 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1473.Widths)
  · have he : Geometry.b1473.half 0 false=Geometry.b2121 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2121
  · have he : Geometry.b1473.half 0 true=Geometry.b2122 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2122

theorem bound1050 : BoxMajorant Geometry.b1050 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1050.Widths)
  · have he : Geometry.b1050.half 2 false=Geometry.b1473 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1473
  · have he : Geometry.b1050.half 2 true=Geometry.b1474 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1474

theorem bound1049 : BoxMajorant Geometry.b1049 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1049 0 (by decide +kernel) x hx hd ho).elim

theorem bound762 : BoxMajorant Geometry.b762 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b762 0 (by decide +kernel) x hx hd ho).elim

theorem bound761 : BoxMajorant Geometry.b761 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b761.Widths)
  · have he : Geometry.b761.half 1 false=Geometry.b1049 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1049
  · have he : Geometry.b761.half 1 true=Geometry.b1050 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1050

theorem bound488 : BoxMajorant Geometry.b488 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b488.Widths)
  · have he : Geometry.b488.half 0 false=Geometry.b761 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound761
  · have he : Geometry.b488.half 0 true=Geometry.b762 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound762

end N7.Kernel.Cover
