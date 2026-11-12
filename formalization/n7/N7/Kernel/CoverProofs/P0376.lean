import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.PositiveGroups.G0418
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4942 : BoxMajorant Geometry.b4942 := by
  exact PositiveLeaves.L1712.bound

theorem bound4941 : BoxMajorant Geometry.b4941 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4941 2 (by decide +kernel) x hx hd ho).elim

theorem bound4595 : BoxMajorant Geometry.b4595 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4595.Widths)
  · have he : Geometry.b4595.half 2 false=Geometry.b4941 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4941
  · have he : Geometry.b4595.half 2 true=Geometry.b4942 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4942

end N7.Kernel.Cover
