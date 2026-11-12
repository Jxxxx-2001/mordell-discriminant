import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0030
import N7.Kernel.PositiveGroups.G0194
import N7.Kernel.PositiveGroups.G0195
import N7.Kernel.PositiveGroups.G0234
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1966 : BoxMajorant Geometry.b1966 := by
  exact PositiveLeaves.L593.bound

theorem bound1965 : BoxMajorant Geometry.b1965 := by
  exact PositiveLeaves.L594.bound

theorem bound1964 : BoxMajorant Geometry.b1964 := by
  exact PositiveLeaves.L596.bound

theorem bound1963 : BoxMajorant Geometry.b1963 := by
  exact PositiveLeaves.L597.bound

theorem bound1354 : BoxMajorant Geometry.b1354 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1354.Widths)
  · have he : Geometry.b1354.half 2 false=Geometry.b1965 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1965
  · have he : Geometry.b1354.half 2 true=Geometry.b1966 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1966

theorem bound1353 : BoxMajorant Geometry.b1353 := by
  exact PositiveLeaves.L595.bound

theorem bound1352 : BoxMajorant Geometry.b1352 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1352.Widths)
  · have he : Geometry.b1352.half 2 false=Geometry.b1963 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1963
  · have he : Geometry.b1352.half 2 true=Geometry.b1964 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1964

theorem bound1351 : BoxMajorant Geometry.b1351 := by
  exact PositiveLeaves.L598.bound

theorem bound966 : BoxMajorant Geometry.b966 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b966.Widths)
  · have he : Geometry.b966.half 1 false=Geometry.b1353 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1353
  · have he : Geometry.b966.half 1 true=Geometry.b1354 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1354

theorem bound965 : BoxMajorant Geometry.b965 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b965.Widths)
  · have he : Geometry.b965.half 1 false=Geometry.b1351 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1351
  · have he : Geometry.b965.half 1 true=Geometry.b1352 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1352

theorem bound672 : BoxMajorant Geometry.b672 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b672.Widths)
  · have he : Geometry.b672.half 0 false=Geometry.b965 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound965
  · have he : Geometry.b672.half 0 true=Geometry.b966 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound966

end N7.Kernel.Cover
