import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.PositiveGroups.G0054
import N7.Kernel.PositiveGroups.G0121
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1846 : BoxMajorant Geometry.b1846 := by
  exact PositiveLeaves.L810.bound

theorem bound1845 : BoxMajorant Geometry.b1845 := by
  exact PositiveLeaves.L811.bound

theorem bound1844 : BoxMajorant Geometry.b1844 := by
  exact PositiveLeaves.L812.bound

theorem bound1843 : BoxMajorant Geometry.b1843 := by
  exact PositiveLeaves.L813.bound

theorem bound1282 : BoxMajorant Geometry.b1282 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1282.Widths)
  · have he : Geometry.b1282.half 2 false=Geometry.b1845 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1845
  · have he : Geometry.b1282.half 2 true=Geometry.b1846 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1846

theorem bound1281 : BoxMajorant Geometry.b1281 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1281.Widths)
  · have he : Geometry.b1281.half 2 false=Geometry.b1843 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1843
  · have he : Geometry.b1281.half 2 true=Geometry.b1844 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1844

theorem bound926 : BoxMajorant Geometry.b926 := by
  exact PositiveLeaves.L809.bound

theorem bound925 : BoxMajorant Geometry.b925 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b925.Widths)
  · have he : Geometry.b925.half 1 false=Geometry.b1281 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1281
  · have he : Geometry.b925.half 1 true=Geometry.b1282 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1282

theorem bound637 : BoxMajorant Geometry.b637 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b637.Widths)
  · have he : Geometry.b637.half 0 false=Geometry.b925 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound925
  · have he : Geometry.b637.half 0 true=Geometry.b926 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound926

end N7.Kernel.Cover
