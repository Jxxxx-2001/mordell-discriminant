import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.PositiveGroups.G0185
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3222 : BoxMajorant Geometry.b3222 := by
  exact PositiveLeaves.L2502.bound

theorem bound3221 : BoxMajorant Geometry.b3221 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3221 2 (by decide +kernel) x hx hd ho).elim

theorem bound2859 : BoxMajorant Geometry.b2859 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2859.Widths)
  · have he : Geometry.b2859.half 0 false=Geometry.b3221 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3221
  · have he : Geometry.b2859.half 0 true=Geometry.b3222 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3222

end N7.Kernel.Cover
