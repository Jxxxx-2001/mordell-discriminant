import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.PositiveGroups.G0175
import N7.Kernel.PositiveGroups.G0176
import N7.Kernel.PositiveGroups.G0218
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2036 : BoxMajorant Geometry.b2036 := by
  exact PositiveLeaves.L140.bound

theorem bound2035 : BoxMajorant Geometry.b2035 := by
  exact PositiveLeaves.L141.bound

theorem bound2034 : BoxMajorant Geometry.b2034 := by
  exact PositiveLeaves.L142.bound

theorem bound2033 : BoxMajorant Geometry.b2033 := by
  exact PositiveLeaves.L143.bound

theorem bound2032 : BoxMajorant Geometry.b2032 := by
  exact PositiveLeaves.L144.bound

theorem bound2031 : BoxMajorant Geometry.b2031 := by
  exact PositiveLeaves.L145.bound

theorem bound2030 : BoxMajorant Geometry.b2030 := by
  exact PositiveLeaves.L146.bound

theorem bound2029 : BoxMajorant Geometry.b2029 := by
  exact PositiveLeaves.L147.bound

theorem bound1400 : BoxMajorant Geometry.b1400 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1400.Widths)
  · have he : Geometry.b1400.half 2 false=Geometry.b2035 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2035
  · have he : Geometry.b1400.half 2 true=Geometry.b2036 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2036

theorem bound1399 : BoxMajorant Geometry.b1399 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1399.Widths)
  · have he : Geometry.b1399.half 2 false=Geometry.b2033 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2033
  · have he : Geometry.b1399.half 2 true=Geometry.b2034 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2034

theorem bound1398 : BoxMajorant Geometry.b1398 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1398.Widths)
  · have he : Geometry.b1398.half 2 false=Geometry.b2031 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2031
  · have he : Geometry.b1398.half 2 true=Geometry.b2032 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2032

theorem bound1397 : BoxMajorant Geometry.b1397 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1397.Widths)
  · have he : Geometry.b1397.half 2 false=Geometry.b2029 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2029
  · have he : Geometry.b1397.half 2 true=Geometry.b2030 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2030

theorem bound996 : BoxMajorant Geometry.b996 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b996.Widths)
  · have he : Geometry.b996.half 1 false=Geometry.b1399 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1399
  · have he : Geometry.b996.half 1 true=Geometry.b1400 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1400

theorem bound995 : BoxMajorant Geometry.b995 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b995.Widths)
  · have he : Geometry.b995.half 1 false=Geometry.b1397 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1397
  · have he : Geometry.b995.half 1 true=Geometry.b1398 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1398

theorem bound696 : BoxMajorant Geometry.b696 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b696.Widths)
  · have he : Geometry.b696.half 0 false=Geometry.b995 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound995
  · have he : Geometry.b696.half 0 true=Geometry.b996 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound996

end N7.Kernel.Cover
