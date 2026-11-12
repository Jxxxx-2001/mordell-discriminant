import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.PositiveGroups.G0054
import N7.Kernel.PositiveGroups.G0084
import N7.Kernel.PositiveGroups.G0120
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1842 : BoxMajorant Geometry.b1842 := by
  exact PositiveLeaves.L818.bound

theorem bound1841 : BoxMajorant Geometry.b1841 := by
  exact PositiveLeaves.L819.bound

theorem bound1280 : BoxMajorant Geometry.b1280 := by
  exact PositiveLeaves.L817.bound

theorem bound1279 : BoxMajorant Geometry.b1279 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1279.Widths)
  · have he : Geometry.b1279.half 2 false=Geometry.b1841 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1841
  · have he : Geometry.b1279.half 2 true=Geometry.b1842 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1842

theorem bound924 : BoxMajorant Geometry.b924 := by
  exact PositiveLeaves.L816.bound

theorem bound923 : BoxMajorant Geometry.b923 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b923.Widths)
  · have he : Geometry.b923.half 1 false=Geometry.b1279 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1279
  · have he : Geometry.b923.half 1 true=Geometry.b1280 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1280

theorem bound634 : BoxMajorant Geometry.b634 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b634.Widths)
  · have he : Geometry.b634.half 0 false=Geometry.b923 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound923
  · have he : Geometry.b634.half 0 true=Geometry.b924 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound924

end N7.Kernel.Cover
