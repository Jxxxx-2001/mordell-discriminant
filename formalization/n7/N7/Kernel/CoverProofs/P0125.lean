import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.PositiveGroups.G0161
import N7.Kernel.PositiveGroups.G0162
import N7.Kernel.PositiveGroups.G0209
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1840 : BoxMajorant Geometry.b1840 := by
  exact PositiveLeaves.L824.bound

theorem bound1839 : BoxMajorant Geometry.b1839 := by
  exact PositiveLeaves.L825.bound

theorem bound1838 : BoxMajorant Geometry.b1838 := by
  exact PositiveLeaves.L826.bound

theorem bound1837 : BoxMajorant Geometry.b1837 := by
  exact PositiveLeaves.L827.bound

theorem bound1836 : BoxMajorant Geometry.b1836 := by
  exact PositiveLeaves.L828.bound

theorem bound1835 : BoxMajorant Geometry.b1835 := by
  exact PositiveLeaves.L829.bound

theorem bound1834 : BoxMajorant Geometry.b1834 := by
  exact PositiveLeaves.L830.bound

theorem bound1833 : BoxMajorant Geometry.b1833 := by
  exact PositiveLeaves.L831.bound

theorem bound1276 : BoxMajorant Geometry.b1276 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1276.Widths)
  · have he : Geometry.b1276.half 2 false=Geometry.b1839 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1839
  · have he : Geometry.b1276.half 2 true=Geometry.b1840 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1840

theorem bound1275 : BoxMajorant Geometry.b1275 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1275.Widths)
  · have he : Geometry.b1275.half 2 false=Geometry.b1837 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1837
  · have he : Geometry.b1275.half 2 true=Geometry.b1838 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1838

theorem bound1274 : BoxMajorant Geometry.b1274 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1274.Widths)
  · have he : Geometry.b1274.half 2 false=Geometry.b1835 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1835
  · have he : Geometry.b1274.half 2 true=Geometry.b1836 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1836

theorem bound1273 : BoxMajorant Geometry.b1273 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1273.Widths)
  · have he : Geometry.b1273.half 2 false=Geometry.b1833 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1833
  · have he : Geometry.b1273.half 2 true=Geometry.b1834 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1834

theorem bound920 : BoxMajorant Geometry.b920 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b920.Widths)
  · have he : Geometry.b920.half 1 false=Geometry.b1275 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1275
  · have he : Geometry.b920.half 1 true=Geometry.b1276 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1276

theorem bound919 : BoxMajorant Geometry.b919 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b919.Widths)
  · have he : Geometry.b919.half 1 false=Geometry.b1273 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1273
  · have he : Geometry.b919.half 1 true=Geometry.b1274 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1274

theorem bound631 : BoxMajorant Geometry.b631 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b631.Widths)
  · have he : Geometry.b631.half 0 false=Geometry.b919 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound919
  · have he : Geometry.b631.half 0 true=Geometry.b920 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound920

end N7.Kernel.Cover
