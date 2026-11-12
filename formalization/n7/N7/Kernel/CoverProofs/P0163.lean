import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.PositiveGroups.G0217
import N7.Kernel.PositiveGroups.G0219
import N7.Kernel.PositiveGroups.G0255
import N7.Kernel.PositiveGroups.G0283
import N7.Kernel.PositiveGroups.G0284
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3180 : BoxMajorant Geometry.b3180 := by
  exact PositiveLeaves.L135.bound

theorem bound3179 : BoxMajorant Geometry.b3179 := by
  exact PositiveLeaves.L136.bound

theorem bound3178 : BoxMajorant Geometry.b3178 := by
  exact PositiveLeaves.L138.bound

theorem bound3177 : BoxMajorant Geometry.b3177 := by
  exact PositiveLeaves.L139.bound

theorem bound2782 : BoxMajorant Geometry.b2782 := by
  exact PositiveLeaves.L134.bound

theorem bound2781 : BoxMajorant Geometry.b2781 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2781.Widths)
  · have he : Geometry.b2781.half 2 false=Geometry.b3179 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3179
  · have he : Geometry.b2781.half 2 true=Geometry.b3180 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3180

theorem bound2780 : BoxMajorant Geometry.b2780 := by
  exact PositiveLeaves.L137.bound

theorem bound2779 : BoxMajorant Geometry.b2779 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2779.Widths)
  · have he : Geometry.b2779.half 2 false=Geometry.b3177 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3177
  · have he : Geometry.b2779.half 2 true=Geometry.b3178 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3178

theorem bound2442 : BoxMajorant Geometry.b2442 := by
  exact PositiveLeaves.L129.bound

theorem bound2441 : BoxMajorant Geometry.b2441 := by
  exact PositiveLeaves.L130.bound

theorem bound2440 : BoxMajorant Geometry.b2440 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2440.Widths)
  · have he : Geometry.b2440.half 1 false=Geometry.b2781 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2781
  · have he : Geometry.b2440.half 1 true=Geometry.b2782 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2782

theorem bound2439 : BoxMajorant Geometry.b2439 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2439.Widths)
  · have he : Geometry.b2439.half 1 false=Geometry.b2779 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2779
  · have he : Geometry.b2439.half 1 true=Geometry.b2780 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2780

theorem bound2044 : BoxMajorant Geometry.b2044 := by
  exact PositiveLeaves.L126.bound

theorem bound2043 : BoxMajorant Geometry.b2043 := by
  exact PositiveLeaves.L127.bound

theorem bound2042 : BoxMajorant Geometry.b2042 := by
  exact PositiveLeaves.L128.bound

theorem bound2041 : BoxMajorant Geometry.b2041 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2041.Widths)
  · have he : Geometry.b2041.half 0 false=Geometry.b2441 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2441
  · have he : Geometry.b2041.half 0 true=Geometry.b2442 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2442

theorem bound2040 : BoxMajorant Geometry.b2040 := by
  exact PositiveLeaves.L131.bound

theorem bound2039 : BoxMajorant Geometry.b2039 := by
  exact PositiveLeaves.L132.bound

theorem bound2038 : BoxMajorant Geometry.b2038 := by
  exact PositiveLeaves.L133.bound

theorem bound2037 : BoxMajorant Geometry.b2037 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2037.Widths)
  · have he : Geometry.b2037.half 0 false=Geometry.b2439 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2439
  · have he : Geometry.b2037.half 0 true=Geometry.b2440 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2440

theorem bound1404 : BoxMajorant Geometry.b1404 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1404.Widths)
  · have he : Geometry.b1404.half 2 false=Geometry.b2043 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2043
  · have he : Geometry.b1404.half 2 true=Geometry.b2044 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2044

theorem bound1403 : BoxMajorant Geometry.b1403 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1403.Widths)
  · have he : Geometry.b1403.half 2 false=Geometry.b2041 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2041
  · have he : Geometry.b1403.half 2 true=Geometry.b2042 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2042

theorem bound1402 : BoxMajorant Geometry.b1402 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1402.Widths)
  · have he : Geometry.b1402.half 2 false=Geometry.b2039 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2039
  · have he : Geometry.b1402.half 2 true=Geometry.b2040 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2040

theorem bound1401 : BoxMajorant Geometry.b1401 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1401.Widths)
  · have he : Geometry.b1401.half 2 false=Geometry.b2037 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2037
  · have he : Geometry.b1401.half 2 true=Geometry.b2038 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2038

theorem bound998 : BoxMajorant Geometry.b998 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b998.Widths)
  · have he : Geometry.b998.half 1 false=Geometry.b1403 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1403
  · have he : Geometry.b998.half 1 true=Geometry.b1404 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1404

theorem bound997 : BoxMajorant Geometry.b997 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b997.Widths)
  · have he : Geometry.b997.half 1 false=Geometry.b1401 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1401
  · have he : Geometry.b997.half 1 true=Geometry.b1402 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1402

theorem bound697 : BoxMajorant Geometry.b697 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b697.Widths)
  · have he : Geometry.b697.half 0 false=Geometry.b997 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound997
  · have he : Geometry.b697.half 0 true=Geometry.b998 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound998

end N7.Kernel.Cover
