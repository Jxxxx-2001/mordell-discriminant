import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.PositiveGroups.G0147
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3230 : BoxMajorant Geometry.b3230 := by
  exact PositiveLeaves.L2474.bound

theorem bound3229 : BoxMajorant Geometry.b3229 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3229 2 (by decide +kernel) x hx hd ho).elim

theorem bound2867 : BoxMajorant Geometry.b2867 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2867.Widths)
  · have he : Geometry.b2867.half 0 false=Geometry.b3229 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3229
  · have he : Geometry.b2867.half 0 true=Geometry.b3230 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3230

end N7.Kernel.Cover
