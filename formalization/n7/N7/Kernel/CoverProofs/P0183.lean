import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0061
import N7.Kernel.PositiveGroups.G0095
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2088 : BoxMajorant Geometry.b2088 := by
  exact PositiveLeaves.L26.bound

theorem bound2087 : BoxMajorant Geometry.b2087 := by
  exact PositiveLeaves.L27.bound

theorem bound1438 : BoxMajorant Geometry.b1438 := by
  exact PositiveLeaves.L25.bound

theorem bound1437 : BoxMajorant Geometry.b1437 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1437.Widths)
  · have he : Geometry.b1437.half 2 false=Geometry.b2087 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2087
  · have he : Geometry.b1437.half 2 true=Geometry.b2088 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2088

theorem bound1022 : BoxMajorant Geometry.b1022 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1022.Widths)
  · have he : Geometry.b1022.half 1 false=Geometry.b1437 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1437
  · have he : Geometry.b1022.half 1 true=Geometry.b1438 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1438

end N7.Kernel.Cover
