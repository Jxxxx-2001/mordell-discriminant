import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.PositiveGroups.G0129
import N7.Kernel.PositiveGroups.G0130
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1746 : BoxMajorant Geometry.b1746 := by
  exact PositiveLeaves.L1080.bound

theorem bound1745 : BoxMajorant Geometry.b1745 := by
  exact PositiveLeaves.L1081.bound

theorem bound1744 : BoxMajorant Geometry.b1744 := by
  exact PositiveLeaves.L1082.bound

theorem bound1743 : BoxMajorant Geometry.b1743 := by
  exact PositiveLeaves.L1083.bound

theorem bound1224 : BoxMajorant Geometry.b1224 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1224.Widths)
  · have he : Geometry.b1224.half 2 false=Geometry.b1745 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1745
  · have he : Geometry.b1224.half 2 true=Geometry.b1746 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1746

theorem bound1223 : BoxMajorant Geometry.b1223 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1223.Widths)
  · have he : Geometry.b1223.half 2 false=Geometry.b1743 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1743
  · have he : Geometry.b1223.half 2 true=Geometry.b1744 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1744

theorem bound888 : BoxMajorant Geometry.b888 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b888.Widths)
  · have he : Geometry.b888.half 1 false=Geometry.b1223 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1223
  · have he : Geometry.b888.half 1 true=Geometry.b1224 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1224

end N7.Kernel.Cover
