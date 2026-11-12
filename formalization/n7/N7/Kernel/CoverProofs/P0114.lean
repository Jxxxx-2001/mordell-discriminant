import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.PositiveGroups.G0088
import N7.Kernel.PositiveGroups.G0128
import N7.Kernel.PositiveGroups.G0129
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1754 : BoxMajorant Geometry.b1754 := by
  exact PositiveLeaves.L1071.bound

theorem bound1753 : BoxMajorant Geometry.b1753 := by
  exact PositiveLeaves.L1072.bound

theorem bound1752 : BoxMajorant Geometry.b1752 := by
  exact PositiveLeaves.L1073.bound

theorem bound1751 : BoxMajorant Geometry.b1751 := by
  exact PositiveLeaves.L1074.bound

theorem bound1228 : BoxMajorant Geometry.b1228 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1228.Widths)
  · have he : Geometry.b1228.half 2 false=Geometry.b1753 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1753
  · have he : Geometry.b1228.half 2 true=Geometry.b1754 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1754

theorem bound1227 : BoxMajorant Geometry.b1227 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1227.Widths)
  · have he : Geometry.b1227.half 2 false=Geometry.b1751 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1751
  · have he : Geometry.b1227.half 2 true=Geometry.b1752 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1752

theorem bound890 : BoxMajorant Geometry.b890 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b890.Widths)
  · have he : Geometry.b890.half 1 false=Geometry.b1227 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1227
  · have he : Geometry.b890.half 1 true=Geometry.b1228 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1228

end N7.Kernel.Cover
