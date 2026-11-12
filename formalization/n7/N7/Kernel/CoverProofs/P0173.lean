import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0062
import N7.Kernel.PositiveGroups.G0095
import N7.Kernel.PositiveGroups.G0096
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2060 : BoxMajorant Geometry.b2060 := by
  exact PositiveLeaves.L67.bound

theorem bound2059 : BoxMajorant Geometry.b2059 := by
  exact PositiveLeaves.L68.bound

theorem bound1418 : BoxMajorant Geometry.b1418 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1418.Widths)
  · have he : Geometry.b1418.half 2 false=Geometry.b2059 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2059
  · have he : Geometry.b1418.half 2 true=Geometry.b2060 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2060

theorem bound1417 : BoxMajorant Geometry.b1417 := by
  exact PositiveLeaves.L69.bound

theorem bound1011 : BoxMajorant Geometry.b1011 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1011.Widths)
  · have he : Geometry.b1011.half 1 false=Geometry.b1417 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1417
  · have he : Geometry.b1011.half 1 true=Geometry.b1418 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1418

end N7.Kernel.Cover
