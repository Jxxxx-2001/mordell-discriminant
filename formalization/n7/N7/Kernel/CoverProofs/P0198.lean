import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.PositiveGroups.G0188
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2844 : BoxMajorant Geometry.b2844 := by
  exact PositiveLeaves.L2566.bound

theorem bound2843 : BoxMajorant Geometry.b2843 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2843 2 (by decide +kernel) x hx hd ho).elim

theorem bound2492 : BoxMajorant Geometry.b2492 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2492.Widths)
  · have he : Geometry.b2492.half 2 false=Geometry.b2843 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2843
  · have he : Geometry.b2492.half 2 true=Geometry.b2844 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2844

end N7.Kernel.Cover
