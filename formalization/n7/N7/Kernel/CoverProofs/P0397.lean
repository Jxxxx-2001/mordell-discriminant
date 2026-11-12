import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.PositiveGroups.G0458
import N7.Kernel.PositiveGroups.G0459
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5078 : BoxMajorant Geometry.b5078 := by
  exact PositiveLeaves.L259.bound

theorem bound5077 : BoxMajorant Geometry.b5077 := by
  exact PositiveLeaves.L260.bound

theorem bound4695 : BoxMajorant Geometry.b4695 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4695.Widths)
  · have he : Geometry.b4695.half 2 false=Geometry.b5077 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5077
  · have he : Geometry.b4695.half 2 true=Geometry.b5078 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5078

end N7.Kernel.Cover
