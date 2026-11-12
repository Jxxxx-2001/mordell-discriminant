import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.PositiveGroups.G0063
import N7.Kernel.PositiveGroups.G0097
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1414 : BoxMajorant Geometry.b1414 := by
  exact PositiveLeaves.L106.bound

theorem bound1413 : BoxMajorant Geometry.b1413 := by
  exact PositiveLeaves.L107.bound

theorem bound1006 : BoxMajorant Geometry.b1006 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1006.Widths)
  · have he : Geometry.b1006.half 1 false=Geometry.b1413 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1413
  · have he : Geometry.b1006.half 1 true=Geometry.b1414 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1414

theorem bound1005 : BoxMajorant Geometry.b1005 := by
  exact PositiveLeaves.L108.bound

theorem bound701 : BoxMajorant Geometry.b701 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b701.Widths)
  · have he : Geometry.b701.half 0 false=Geometry.b1005 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1005
  · have he : Geometry.b701.half 0 true=Geometry.b1006 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1006

end N7.Kernel.Cover
