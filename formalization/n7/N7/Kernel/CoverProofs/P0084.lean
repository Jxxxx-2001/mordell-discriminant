import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.PositiveGroups.G0155
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2660 : BoxMajorant Geometry.b2660 := by
  exact PositiveLeaves.L1247.bound

theorem bound2659 : BoxMajorant Geometry.b2659 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2659 0 (by decide +kernel) x hx hd ho).elim

theorem bound2287 : BoxMajorant Geometry.b2287 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2287.Widths)
  · have he : Geometry.b2287.half 1 false=Geometry.b2659 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2659
  · have he : Geometry.b2287.half 1 true=Geometry.b2660 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2660

end N7.Kernel.Cover
