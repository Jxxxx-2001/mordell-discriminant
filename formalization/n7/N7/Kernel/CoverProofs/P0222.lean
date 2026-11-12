import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.PositiveGroups.G0265
import N7.Kernel.PositiveGroups.G0294
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3826 : BoxMajorant Geometry.b3826 := by
  exact PositiveLeaves.L2153.bound

theorem bound3825 : BoxMajorant Geometry.b3825 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3825 2 (by decide +kernel) x hx hd ho).elim

theorem bound3524 : BoxMajorant Geometry.b3524 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3524.Widths)
  · have he : Geometry.b3524.half 2 false=Geometry.b3825 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3825
  · have he : Geometry.b3524.half 2 true=Geometry.b3826 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3826

theorem bound3523 : BoxMajorant Geometry.b3523 := by
  exact PositiveLeaves.L2155.bound

theorem bound3250 : BoxMajorant Geometry.b3250 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3250.Widths)
  · have he : Geometry.b3250.half 1 false=Geometry.b3523 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3523
  · have he : Geometry.b3250.half 1 true=Geometry.b3524 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3524

end N7.Kernel.Cover
