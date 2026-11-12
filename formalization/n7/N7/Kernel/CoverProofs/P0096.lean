import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.PositiveGroups.G0135
import N7.Kernel.PositiveGroups.G0136
import N7.Kernel.PositiveGroups.G0171
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1698 : BoxMajorant Geometry.b1698 := by
  exact PositiveLeaves.L1151.bound

theorem bound1697 : BoxMajorant Geometry.b1697 := by
  exact PositiveLeaves.L1152.bound

theorem bound1696 : BoxMajorant Geometry.b1696 := by
  exact PositiveLeaves.L1153.bound

theorem bound1695 : BoxMajorant Geometry.b1695 := by
  exact PositiveLeaves.L1154.bound

theorem bound1196 : BoxMajorant Geometry.b1196 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1196.Widths)
  · have he : Geometry.b1196.half 2 false=Geometry.b1697 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1697
  · have he : Geometry.b1196.half 2 true=Geometry.b1698 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1698

theorem bound1195 : BoxMajorant Geometry.b1195 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1195.Widths)
  · have he : Geometry.b1195.half 2 false=Geometry.b1695 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1695
  · have he : Geometry.b1195.half 2 true=Geometry.b1696 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1696

theorem bound870 : BoxMajorant Geometry.b870 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b870.Widths)
  · have he : Geometry.b870.half 1 false=Geometry.b1195 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1195
  · have he : Geometry.b870.half 1 true=Geometry.b1196 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1196

end N7.Kernel.Cover
