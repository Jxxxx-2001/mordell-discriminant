import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.PositiveGroups.G0031
import N7.Kernel.PositiveGroups.G0032
import N7.Kernel.PositiveGroups.G0057
import N7.Kernel.PositiveGroups.G0058
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2304 : BoxMajorant Geometry.b2304 := by
  exact PositiveLeaves.L1122.bound

theorem bound2303 : BoxMajorant Geometry.b2303 := by
  exact PositiveLeaves.L1123.bound

theorem bound1720 : BoxMajorant Geometry.b1720 := by
  exact PositiveLeaves.L1119.bound

theorem bound1719 : BoxMajorant Geometry.b1719 := by
  exact PositiveLeaves.L1120.bound

theorem bound1718 : BoxMajorant Geometry.b1718 := by
  exact PositiveLeaves.L1121.bound

theorem bound1717 : BoxMajorant Geometry.b1717 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1717.Widths)
  · have he : Geometry.b1717.half 0 false=Geometry.b2303 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2303
  · have he : Geometry.b1717.half 0 true=Geometry.b2304 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2304

theorem bound1208 : BoxMajorant Geometry.b1208 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1208.Widths)
  · have he : Geometry.b1208.half 2 false=Geometry.b1719 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1719
  · have he : Geometry.b1208.half 2 true=Geometry.b1720 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1720

theorem bound1207 : BoxMajorant Geometry.b1207 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1207.Widths)
  · have he : Geometry.b1207.half 2 false=Geometry.b1717 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1717
  · have he : Geometry.b1207.half 2 true=Geometry.b1718 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1718

theorem bound876 : BoxMajorant Geometry.b876 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b876.Widths)
  · have he : Geometry.b876.half 1 false=Geometry.b1207 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1207
  · have he : Geometry.b876.half 1 true=Geometry.b1208 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1208

end N7.Kernel.Cover
