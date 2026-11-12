import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.PositiveGroups.G0099
import N7.Kernel.PositiveGroups.G0100
import N7.Kernel.PositiveGroups.G0141
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2006 : BoxMajorant Geometry.b2006 := by
  exact PositiveLeaves.L513.bound

theorem bound2005 : BoxMajorant Geometry.b2005 := by
  exact PositiveLeaves.L514.bound

theorem bound2004 : BoxMajorant Geometry.b2004 := by
  exact PositiveLeaves.L515.bound

theorem bound2003 : BoxMajorant Geometry.b2003 := by
  exact PositiveLeaves.L516.bound

theorem bound1382 : BoxMajorant Geometry.b1382 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1382.Widths)
  · have he : Geometry.b1382.half 2 false=Geometry.b2005 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2005
  · have he : Geometry.b1382.half 2 true=Geometry.b2006 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2006

theorem bound1381 : BoxMajorant Geometry.b1381 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1381.Widths)
  · have he : Geometry.b1381.half 2 false=Geometry.b2003 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2003
  · have he : Geometry.b1381.half 2 true=Geometry.b2004 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2004

theorem bound984 : BoxMajorant Geometry.b984 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b984.Widths)
  · have he : Geometry.b984.half 1 false=Geometry.b1381 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1381
  · have he : Geometry.b984.half 1 true=Geometry.b1382 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1382

end N7.Kernel.Cover
