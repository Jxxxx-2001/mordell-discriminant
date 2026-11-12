import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.PositiveGroups.G0259
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4054 : BoxMajorant Geometry.b4054 := by
  exact PositiveLeaves.L1372.bound

theorem bound4053 : BoxMajorant Geometry.b4053 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4053 2 (by decide +kernel) x hx hd ho).elim

theorem bound3657 : BoxMajorant Geometry.b3657 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3657.Widths)
  · have he : Geometry.b3657.half 2 false=Geometry.b4053 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4053
  · have he : Geometry.b3657.half 2 true=Geometry.b4054 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4054

end N7.Kernel.Cover
