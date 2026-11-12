import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.PositiveGroups.G0092
import N7.Kernel.PositiveGroups.G0093
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1686 : BoxMajorant Geometry.b1686 := by
  exact PositiveLeaves.L1167.bound

theorem bound1685 : BoxMajorant Geometry.b1685 := by
  exact PositiveLeaves.L1168.bound

theorem bound1684 : BoxMajorant Geometry.b1684 := by
  exact PositiveLeaves.L1169.bound

theorem bound1683 : BoxMajorant Geometry.b1683 := by
  exact PositiveLeaves.L1170.bound

theorem bound1190 : BoxMajorant Geometry.b1190 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1190.Widths)
  · have he : Geometry.b1190.half 2 false=Geometry.b1685 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1685
  · have he : Geometry.b1190.half 2 true=Geometry.b1686 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1686

theorem bound1189 : BoxMajorant Geometry.b1189 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1189.Widths)
  · have he : Geometry.b1189.half 2 false=Geometry.b1683 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1683
  · have he : Geometry.b1189.half 2 true=Geometry.b1684 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1684

theorem bound867 : BoxMajorant Geometry.b867 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b867.Widths)
  · have he : Geometry.b867.half 1 false=Geometry.b1189 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1189
  · have he : Geometry.b867.half 1 true=Geometry.b1190 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1190

end N7.Kernel.Cover
