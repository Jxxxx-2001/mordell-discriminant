import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.PositiveGroups.G0127
import N7.Kernel.PositiveGroups.G0165
import N7.Kernel.PositiveGroups.G0167
import N7.Kernel.PositiveGroups.G0211
import N7.Kernel.PositiveGroups.G0212
import N7.Kernel.PositiveGroups.G0213
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2690 : BoxMajorant Geometry.b2690 := by
  exact PositiveLeaves.L942.bound

theorem bound2689 : BoxMajorant Geometry.b2689 := by
  exact PositiveLeaves.L943.bound

theorem bound2334 : BoxMajorant Geometry.b2334 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2334.Widths)
  · have he : Geometry.b2334.half 1 false=Geometry.b2689 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2689
  · have he : Geometry.b2334.half 1 true=Geometry.b2690 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2690

theorem bound2333 : BoxMajorant Geometry.b2333 := by
  exact PositiveLeaves.L944.bound

theorem bound1788 : BoxMajorant Geometry.b1788 := by
  exact PositiveLeaves.L941.bound

theorem bound1787 : BoxMajorant Geometry.b1787 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1787.Widths)
  · have he : Geometry.b1787.half 0 false=Geometry.b2333 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2333
  · have he : Geometry.b1787.half 0 true=Geometry.b2334 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2334

theorem bound1786 : BoxMajorant Geometry.b1786 := by
  exact PositiveLeaves.L945.bound

theorem bound1785 : BoxMajorant Geometry.b1785 := by
  exact PositiveLeaves.L946.bound

theorem bound1784 : BoxMajorant Geometry.b1784 := by
  exact PositiveLeaves.L947.bound

theorem bound1783 : BoxMajorant Geometry.b1783 := by
  exact PositiveLeaves.L948.bound

theorem bound1782 : BoxMajorant Geometry.b1782 := by
  exact PositiveLeaves.L949.bound

theorem bound1781 : BoxMajorant Geometry.b1781 := by
  exact PositiveLeaves.L950.bound

theorem bound1248 : BoxMajorant Geometry.b1248 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1248.Widths)
  · have he : Geometry.b1248.half 2 false=Geometry.b1787 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1787
  · have he : Geometry.b1248.half 2 true=Geometry.b1788 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1788

theorem bound1247 : BoxMajorant Geometry.b1247 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1247.Widths)
  · have he : Geometry.b1247.half 2 false=Geometry.b1785 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1785
  · have he : Geometry.b1247.half 2 true=Geometry.b1786 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1786

theorem bound1246 : BoxMajorant Geometry.b1246 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1246.Widths)
  · have he : Geometry.b1246.half 2 false=Geometry.b1783 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1783
  · have he : Geometry.b1246.half 2 true=Geometry.b1784 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1784

theorem bound1245 : BoxMajorant Geometry.b1245 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1245.Widths)
  · have he : Geometry.b1245.half 2 false=Geometry.b1781 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1781
  · have he : Geometry.b1245.half 2 true=Geometry.b1782 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1782

theorem bound904 : BoxMajorant Geometry.b904 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b904.Widths)
  · have he : Geometry.b904.half 1 false=Geometry.b1247 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1247
  · have he : Geometry.b904.half 1 true=Geometry.b1248 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1248

theorem bound903 : BoxMajorant Geometry.b903 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b903.Widths)
  · have he : Geometry.b903.half 1 false=Geometry.b1245 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1245
  · have he : Geometry.b903.half 1 true=Geometry.b1246 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1246

theorem bound620 : BoxMajorant Geometry.b620 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b620.Widths)
  · have he : Geometry.b620.half 0 false=Geometry.b903 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound903
  · have he : Geometry.b620.half 0 true=Geometry.b904 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound904

end N7.Kernel.Cover
