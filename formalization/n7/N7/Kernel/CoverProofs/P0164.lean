import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0218
import N7.Kernel.PositiveGroups.G0253
import N7.Kernel.PositiveGroups.G0254
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2052 : BoxMajorant Geometry.b2052 := by
  exact PositiveLeaves.L118.bound

theorem bound2051 : BoxMajorant Geometry.b2051 := by
  exact PositiveLeaves.L119.bound

theorem bound2050 : BoxMajorant Geometry.b2050 := by
  exact PositiveLeaves.L120.bound

theorem bound2049 : BoxMajorant Geometry.b2049 := by
  exact PositiveLeaves.L121.bound

theorem bound2048 : BoxMajorant Geometry.b2048 := by
  exact PositiveLeaves.L122.bound

theorem bound2047 : BoxMajorant Geometry.b2047 := by
  exact PositiveLeaves.L123.bound

theorem bound2046 : BoxMajorant Geometry.b2046 := by
  exact PositiveLeaves.L124.bound

theorem bound2045 : BoxMajorant Geometry.b2045 := by
  exact PositiveLeaves.L125.bound

theorem bound1408 : BoxMajorant Geometry.b1408 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1408.Widths)
  · have he : Geometry.b1408.half 2 false=Geometry.b2051 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2051
  · have he : Geometry.b1408.half 2 true=Geometry.b2052 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2052

theorem bound1407 : BoxMajorant Geometry.b1407 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1407.Widths)
  · have he : Geometry.b1407.half 2 false=Geometry.b2049 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2049
  · have he : Geometry.b1407.half 2 true=Geometry.b2050 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2050

theorem bound1406 : BoxMajorant Geometry.b1406 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1406.Widths)
  · have he : Geometry.b1406.half 2 false=Geometry.b2047 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2047
  · have he : Geometry.b1406.half 2 true=Geometry.b2048 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2048

theorem bound1405 : BoxMajorant Geometry.b1405 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1405.Widths)
  · have he : Geometry.b1405.half 2 false=Geometry.b2045 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2045
  · have he : Geometry.b1405.half 2 true=Geometry.b2046 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2046

theorem bound1000 : BoxMajorant Geometry.b1000 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1000.Widths)
  · have he : Geometry.b1000.half 1 false=Geometry.b1407 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1407
  · have he : Geometry.b1000.half 1 true=Geometry.b1408 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1408

theorem bound999 : BoxMajorant Geometry.b999 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b999.Widths)
  · have he : Geometry.b999.half 1 false=Geometry.b1405 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1405
  · have he : Geometry.b999.half 1 true=Geometry.b1406 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1406

theorem bound698 : BoxMajorant Geometry.b698 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b698.Widths)
  · have he : Geometry.b698.half 0 false=Geometry.b999 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound999
  · have he : Geometry.b698.half 0 true=Geometry.b1000 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1000

end N7.Kernel.Cover
