import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.PositiveGroups.G0293
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3296 : BoxMajorant Geometry.b3296 := by
  exact PositiveLeaves.L1932.bound

theorem bound3295 : BoxMajorant Geometry.b3295 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3295 2 (by decide +kernel) x hx hd ho).elim

theorem bound2960 : BoxMajorant Geometry.b2960 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2960.Widths)
  · have he : Geometry.b2960.half 0 false=Geometry.b3295 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3295
  · have he : Geometry.b2960.half 0 true=Geometry.b3296 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3296

end N7.Kernel.Cover
