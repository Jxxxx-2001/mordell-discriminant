import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.PositiveGroups.G0261
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3024 : BoxMajorant Geometry.b3024 := by
  exact PositiveLeaves.L1553.bound

theorem bound3023 : BoxMajorant Geometry.b3023 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3023 2 (by decide +kernel) x hx hd ho).elim

theorem bound2626 : BoxMajorant Geometry.b2626 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2626.Widths)
  · have he : Geometry.b2626.half 2 false=Geometry.b3023 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3023
  · have he : Geometry.b2626.half 2 true=Geometry.b3024 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3024

end N7.Kernel.Cover
