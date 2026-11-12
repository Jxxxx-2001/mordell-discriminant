import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.PositiveGroups.G0058
import N7.Kernel.PositiveGroups.G0090
import N7.Kernel.PositiveGroups.G0132
import N7.Kernel.PositiveGroups.G0169
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2674 : BoxMajorant Geometry.b2674 := by
  exact PositiveLeaves.L1127.bound

theorem bound2673 : BoxMajorant Geometry.b2673 := by
  exact PositiveLeaves.L1128.bound

theorem bound2302 : BoxMajorant Geometry.b2302 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2302.Widths)
  · have he : Geometry.b2302.half 1 false=Geometry.b2673 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2673
  · have he : Geometry.b2302.half 1 true=Geometry.b2674 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2674

theorem bound2301 : BoxMajorant Geometry.b2301 := by
  exact PositiveLeaves.L1129.bound

theorem bound1716 : BoxMajorant Geometry.b1716 := by
  exact PositiveLeaves.L1124.bound

theorem bound1715 : BoxMajorant Geometry.b1715 := by
  exact PositiveLeaves.L1125.bound

theorem bound1714 : BoxMajorant Geometry.b1714 := by
  exact PositiveLeaves.L1126.bound

theorem bound1713 : BoxMajorant Geometry.b1713 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1713.Widths)
  · have he : Geometry.b1713.half 0 false=Geometry.b2301 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2301
  · have he : Geometry.b1713.half 0 true=Geometry.b2302 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2302

theorem bound1206 : BoxMajorant Geometry.b1206 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1206.Widths)
  · have he : Geometry.b1206.half 2 false=Geometry.b1715 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1715
  · have he : Geometry.b1206.half 2 true=Geometry.b1716 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1716

theorem bound1205 : BoxMajorant Geometry.b1205 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1205.Widths)
  · have he : Geometry.b1205.half 2 false=Geometry.b1713 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1713
  · have he : Geometry.b1205.half 2 true=Geometry.b1714 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1714

theorem bound875 : BoxMajorant Geometry.b875 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b875.Widths)
  · have he : Geometry.b875.half 1 false=Geometry.b1205 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1205
  · have he : Geometry.b875.half 1 true=Geometry.b1206 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1206

end N7.Kernel.Cover
