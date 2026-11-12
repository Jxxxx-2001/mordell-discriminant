import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.PositiveGroups.G0083
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1848 : BoxMajorant Geometry.b1848 := by
  exact PositiveLeaves.L805.bound

theorem bound1847 : BoxMajorant Geometry.b1847 := by
  exact PositiveLeaves.L806.bound

theorem bound1284 : BoxMajorant Geometry.b1284 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1284.Widths)
  · have he : Geometry.b1284.half 2 false=Geometry.b1847 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1847
  · have he : Geometry.b1284.half 2 true=Geometry.b1848 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1848

theorem bound1283 : BoxMajorant Geometry.b1283 := by
  exact PositiveLeaves.L807.bound

theorem bound928 : BoxMajorant Geometry.b928 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b928.Widths)
  · have he : Geometry.b928.half 1 false=Geometry.b1283 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1283
  · have he : Geometry.b928.half 1 true=Geometry.b1284 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1284

theorem bound927 : BoxMajorant Geometry.b927 := by
  exact PositiveLeaves.L808.bound

theorem bound638 : BoxMajorant Geometry.b638 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b638.Widths)
  · have he : Geometry.b638.half 0 false=Geometry.b927 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound927
  · have he : Geometry.b638.half 0 true=Geometry.b928 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound928

end N7.Kernel.Cover
