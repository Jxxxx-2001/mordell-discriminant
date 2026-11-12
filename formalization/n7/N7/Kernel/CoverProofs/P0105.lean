import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.PositiveGroups.G0031
import N7.Kernel.PositiveGroups.G0056
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound894 : BoxMajorant Geometry.b894 := by
  exact PositiveLeaves.L1063.bound

theorem bound893 : BoxMajorant Geometry.b893 := by
  exact PositiveLeaves.L1064.bound

theorem bound612 : BoxMajorant Geometry.b612 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b612.Widths)
  · have he : Geometry.b612.half 0 false=Geometry.b893 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound893
  · have he : Geometry.b612.half 0 true=Geometry.b894 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound894

end N7.Kernel.Cover
