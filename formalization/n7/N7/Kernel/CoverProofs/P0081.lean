import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.PositiveGroups.G0155
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2654 : BoxMajorant Geometry.b2654 := by
  exact PositiveLeaves.L1258.bound

theorem bound2653 : BoxMajorant Geometry.b2653 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2653 2 (by decide +kernel) x hx hd ho).elim

theorem bound2281 : BoxMajorant Geometry.b2281 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2281.Widths)
  · have he : Geometry.b2281.half 1 false=Geometry.b2653 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2653
  · have he : Geometry.b2281.half 1 true=Geometry.b2654 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2654

end N7.Kernel.Cover
