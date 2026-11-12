import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.PositiveGroups.G0171
import N7.Kernel.PositiveGroups.G0214
import N7.Kernel.PositiveGroups.G0215
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1712 : BoxMajorant Geometry.b1712 := by
  exact PositiveLeaves.L1130.bound

theorem bound1711 : BoxMajorant Geometry.b1711 := by
  exact PositiveLeaves.L1131.bound

theorem bound1710 : BoxMajorant Geometry.b1710 := by
  exact PositiveLeaves.L1132.bound

theorem bound1709 : BoxMajorant Geometry.b1709 := by
  exact PositiveLeaves.L1133.bound

theorem bound1204 : BoxMajorant Geometry.b1204 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1204.Widths)
  · have he : Geometry.b1204.half 2 false=Geometry.b1711 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1711
  · have he : Geometry.b1204.half 2 true=Geometry.b1712 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1712

theorem bound1203 : BoxMajorant Geometry.b1203 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1203.Widths)
  · have he : Geometry.b1203.half 2 false=Geometry.b1709 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1709
  · have he : Geometry.b1203.half 2 true=Geometry.b1710 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1710

theorem bound874 : BoxMajorant Geometry.b874 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b874.Widths)
  · have he : Geometry.b874.half 1 false=Geometry.b1203 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1203
  · have he : Geometry.b874.half 1 true=Geometry.b1204 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1204

end N7.Kernel.Cover
