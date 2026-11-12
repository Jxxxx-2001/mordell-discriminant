import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.PositiveGroups.G0260
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4052 : BoxMajorant Geometry.b4052 := by
  exact PositiveLeaves.L1376.bound

theorem bound4051 : BoxMajorant Geometry.b4051 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4051 2 (by decide +kernel) x hx hd ho).elim

theorem bound3656 : BoxMajorant Geometry.b3656 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3656.Widths)
  · have he : Geometry.b3656.half 2 false=Geometry.b4051 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4051
  · have he : Geometry.b3656.half 2 true=Geometry.b4052 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4052

end N7.Kernel.Cover
