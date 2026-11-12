import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.PositiveGroups.G0089
import N7.Kernel.PositiveGroups.G0090
import N7.Kernel.PositiveGroups.G0129
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1742 : BoxMajorant Geometry.b1742 := by
  exact PositiveLeaves.L1084.bound

theorem bound1741 : BoxMajorant Geometry.b1741 := by
  exact PositiveLeaves.L1085.bound

theorem bound1740 : BoxMajorant Geometry.b1740 := by
  exact PositiveLeaves.L1086.bound

theorem bound1739 : BoxMajorant Geometry.b1739 := by
  exact PositiveLeaves.L1087.bound

theorem bound1222 : BoxMajorant Geometry.b1222 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1222.Widths)
  · have he : Geometry.b1222.half 2 false=Geometry.b1741 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1741
  · have he : Geometry.b1222.half 2 true=Geometry.b1742 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1742

theorem bound1221 : BoxMajorant Geometry.b1221 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1221.Widths)
  · have he : Geometry.b1221.half 2 false=Geometry.b1739 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1739
  · have he : Geometry.b1221.half 2 true=Geometry.b1740 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1740

theorem bound887 : BoxMajorant Geometry.b887 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b887.Widths)
  · have he : Geometry.b887.half 1 false=Geometry.b1221 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1221
  · have he : Geometry.b887.half 1 true=Geometry.b1222 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1222

end N7.Kernel.Cover
