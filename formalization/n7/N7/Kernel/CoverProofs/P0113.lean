import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.PositiveGroups.G0087
import N7.Kernel.PositiveGroups.G0088
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1750 : BoxMajorant Geometry.b1750 := by
  exact PositiveLeaves.L1075.bound

theorem bound1749 : BoxMajorant Geometry.b1749 := by
  exact PositiveLeaves.L1076.bound

theorem bound1748 : BoxMajorant Geometry.b1748 := by
  exact PositiveLeaves.L1077.bound

theorem bound1747 : BoxMajorant Geometry.b1747 := by
  exact PositiveLeaves.L1078.bound

theorem bound1226 : BoxMajorant Geometry.b1226 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1226.Widths)
  · have he : Geometry.b1226.half 2 false=Geometry.b1749 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1749
  · have he : Geometry.b1226.half 2 true=Geometry.b1750 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1750

theorem bound1225 : BoxMajorant Geometry.b1225 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1225.Widths)
  · have he : Geometry.b1225.half 2 false=Geometry.b1747 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1747
  · have he : Geometry.b1225.half 2 true=Geometry.b1748 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1748

theorem bound889 : BoxMajorant Geometry.b889 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b889.Widths)
  · have he : Geometry.b889.half 1 false=Geometry.b1225 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1225
  · have he : Geometry.b889.half 1 true=Geometry.b1226 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1226

end N7.Kernel.Cover
