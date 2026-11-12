import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.PositiveGroups.G0259
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4050 : BoxMajorant Geometry.b4050 := by
  exact PositiveLeaves.L1378.bound

theorem bound4049 : BoxMajorant Geometry.b4049 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4049 2 (by decide +kernel) x hx hd ho).elim

theorem bound3655 : BoxMajorant Geometry.b3655 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3655.Widths)
  · have he : Geometry.b3655.half 2 false=Geometry.b4049 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4049
  · have he : Geometry.b3655.half 2 true=Geometry.b4050 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4050

end N7.Kernel.Cover
