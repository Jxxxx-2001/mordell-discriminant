import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.PositiveGroups.G0226
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3266 : BoxMajorant Geometry.b3266 := by
  exact PositiveLeaves.L2092.bound

theorem bound3265 : BoxMajorant Geometry.b3265 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3265 2 (by decide +kernel) x hx hd ho).elim

theorem bound2938 : BoxMajorant Geometry.b2938 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2938.Widths)
  · have he : Geometry.b2938.half 0 false=Geometry.b3265 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3265
  · have he : Geometry.b2938.half 0 true=Geometry.b3266 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3266

end N7.Kernel.Cover
