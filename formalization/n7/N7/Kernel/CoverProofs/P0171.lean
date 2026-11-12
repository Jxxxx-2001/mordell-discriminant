import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.PositiveGroups.G0098
import N7.Kernel.PositiveGroups.G0099
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2002 : BoxMajorant Geometry.b2002 := by
  exact PositiveLeaves.L517.bound

theorem bound2001 : BoxMajorant Geometry.b2001 := by
  exact PositiveLeaves.L518.bound

theorem bound2000 : BoxMajorant Geometry.b2000 := by
  exact PositiveLeaves.L519.bound

theorem bound1999 : BoxMajorant Geometry.b1999 := by
  exact PositiveLeaves.L520.bound

theorem bound1380 : BoxMajorant Geometry.b1380 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1380.Widths)
  · have he : Geometry.b1380.half 2 false=Geometry.b2001 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2001
  · have he : Geometry.b1380.half 2 true=Geometry.b2002 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2002

theorem bound1379 : BoxMajorant Geometry.b1379 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1379.Widths)
  · have he : Geometry.b1379.half 2 false=Geometry.b1999 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1999
  · have he : Geometry.b1379.half 2 true=Geometry.b2000 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2000

theorem bound983 : BoxMajorant Geometry.b983 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b983.Widths)
  · have he : Geometry.b983.half 1 false=Geometry.b1379 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1379
  · have he : Geometry.b983.half 1 true=Geometry.b1380 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1380

end N7.Kernel.Cover
