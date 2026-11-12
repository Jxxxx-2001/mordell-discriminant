import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.PositiveGroups.G0134
import N7.Kernel.PositiveGroups.G0135
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1694 : BoxMajorant Geometry.b1694 := by
  exact PositiveLeaves.L1155.bound

theorem bound1693 : BoxMajorant Geometry.b1693 := by
  exact PositiveLeaves.L1156.bound

theorem bound1692 : BoxMajorant Geometry.b1692 := by
  exact PositiveLeaves.L1157.bound

theorem bound1691 : BoxMajorant Geometry.b1691 := by
  exact PositiveLeaves.L1158.bound

theorem bound1194 : BoxMajorant Geometry.b1194 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1194.Widths)
  · have he : Geometry.b1194.half 2 false=Geometry.b1693 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1693
  · have he : Geometry.b1194.half 2 true=Geometry.b1694 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1694

theorem bound1193 : BoxMajorant Geometry.b1193 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1193.Widths)
  · have he : Geometry.b1193.half 2 false=Geometry.b1691 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1691
  · have he : Geometry.b1193.half 2 true=Geometry.b1692 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1692

theorem bound869 : BoxMajorant Geometry.b869 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b869.Widths)
  · have he : Geometry.b869.half 1 false=Geometry.b1193 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1193
  · have he : Geometry.b869.half 1 true=Geometry.b1194 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1194

end N7.Kernel.Cover
