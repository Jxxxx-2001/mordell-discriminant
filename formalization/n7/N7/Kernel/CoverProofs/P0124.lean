import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.PositiveGroups.G0087
import N7.Kernel.PositiveGroups.G0125
import N7.Kernel.PositiveGroups.G0162
import N7.Kernel.PositiveGroups.G0163
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2364 : BoxMajorant Geometry.b2364 := by
  exact PositiveLeaves.L836.bound

theorem bound2363 : BoxMajorant Geometry.b2363 := by
  exact PositiveLeaves.L837.bound

theorem bound1832 : BoxMajorant Geometry.b1832 := by
  exact PositiveLeaves.L833.bound

theorem bound1831 : BoxMajorant Geometry.b1831 := by
  exact PositiveLeaves.L834.bound

theorem bound1830 : BoxMajorant Geometry.b1830 := by
  exact PositiveLeaves.L835.bound

theorem bound1829 : BoxMajorant Geometry.b1829 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1829.Widths)
  · have he : Geometry.b1829.half 0 false=Geometry.b2363 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2363
  · have he : Geometry.b1829.half 0 true=Geometry.b2364 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2364

theorem bound1828 : BoxMajorant Geometry.b1828 := by
  exact PositiveLeaves.L838.bound

theorem bound1827 : BoxMajorant Geometry.b1827 := by
  exact PositiveLeaves.L839.bound

theorem bound1272 : BoxMajorant Geometry.b1272 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1272.Widths)
  · have he : Geometry.b1272.half 2 false=Geometry.b1831 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1831
  · have he : Geometry.b1272.half 2 true=Geometry.b1832 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1832

theorem bound1271 : BoxMajorant Geometry.b1271 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1271.Widths)
  · have he : Geometry.b1271.half 2 false=Geometry.b1829 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1829
  · have he : Geometry.b1271.half 2 true=Geometry.b1830 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1830

theorem bound1270 : BoxMajorant Geometry.b1270 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1270.Widths)
  · have he : Geometry.b1270.half 2 false=Geometry.b1827 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1827
  · have he : Geometry.b1270.half 2 true=Geometry.b1828 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1828

theorem bound1269 : BoxMajorant Geometry.b1269 := by
  exact PositiveLeaves.L840.bound

theorem bound918 : BoxMajorant Geometry.b918 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b918.Widths)
  · have he : Geometry.b918.half 1 false=Geometry.b1271 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1271
  · have he : Geometry.b918.half 1 true=Geometry.b1272 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1272

theorem bound917 : BoxMajorant Geometry.b917 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b917.Widths)
  · have he : Geometry.b917.half 1 false=Geometry.b1269 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1269
  · have he : Geometry.b917.half 1 true=Geometry.b1270 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1270

theorem bound629 : BoxMajorant Geometry.b629 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b629.Widths)
  · have he : Geometry.b629.half 0 false=Geometry.b917 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound917
  · have he : Geometry.b629.half 0 true=Geometry.b918 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound918

end N7.Kernel.Cover
