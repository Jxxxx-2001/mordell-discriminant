import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.PositiveGroups.G0070
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1590 : BoxMajorant Geometry.b1590 := by
  exact PositiveLeaves.L2246.bound

theorem bound1589 : BoxMajorant Geometry.b1589 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1589 2 (by decide +kernel) x hx hd ho).elim

theorem bound1588 : BoxMajorant Geometry.b1588 := by
  exact PositiveLeaves.L2248.bound

theorem bound1587 : BoxMajorant Geometry.b1587 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1587 2 (by decide +kernel) x hx hd ho).elim

theorem bound1130 : BoxMajorant Geometry.b1130 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1130.Widths)
  · have he : Geometry.b1130.half 2 false=Geometry.b1589 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1589
  · have he : Geometry.b1130.half 2 true=Geometry.b1590 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1590

theorem bound1129 : BoxMajorant Geometry.b1129 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1129.Widths)
  · have he : Geometry.b1129.half 2 false=Geometry.b1587 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1587
  · have he : Geometry.b1129.half 2 true=Geometry.b1588 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1588

theorem bound820 : BoxMajorant Geometry.b820 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b820.Widths)
  · have he : Geometry.b820.half 1 false=Geometry.b1129 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1129
  · have he : Geometry.b820.half 1 true=Geometry.b1130 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1130

theorem bound819 : BoxMajorant Geometry.b819 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b819 2 (by decide +kernel) x hx hd ho).elim

theorem bound540 : BoxMajorant Geometry.b540 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b540.Widths)
  · have he : Geometry.b540.half 0 false=Geometry.b819 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound819
  · have he : Geometry.b540.half 0 true=Geometry.b820 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound820

end N7.Kernel.Cover
