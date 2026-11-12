import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.PositiveGroups.G0041
import N7.Kernel.PositiveGroups.G0066
import N7.Kernel.PositiveGroups.G0101
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2544 : BoxMajorant Geometry.b2544 := by
  exact PositiveLeaves.L2328.bound

theorem bound2543 : BoxMajorant Geometry.b2543 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2543 2 (by decide +kernel) x hx hd ho).elim

theorem bound2184 : BoxMajorant Geometry.b2184 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2184.Widths)
  · have he : Geometry.b2184.half 1 false=Geometry.b2543 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2543
  · have he : Geometry.b2184.half 1 true=Geometry.b2544 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2544

theorem bound2183 : BoxMajorant Geometry.b2183 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2183 2 (by decide +kernel) x hx hd ho).elim

theorem bound1564 : BoxMajorant Geometry.b1564 := by
  exact PositiveLeaves.L2327.bound

theorem bound1563 : BoxMajorant Geometry.b1563 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1563.Widths)
  · have he : Geometry.b1563.half 0 false=Geometry.b2183 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2183
  · have he : Geometry.b1563.half 0 true=Geometry.b2184 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2184

theorem bound1562 : BoxMajorant Geometry.b1562 := by
  exact PositiveLeaves.L2331.bound

theorem bound1561 : BoxMajorant Geometry.b1561 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1561 2 (by decide +kernel) x hx hd ho).elim

theorem bound1112 : BoxMajorant Geometry.b1112 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1112.Widths)
  · have he : Geometry.b1112.half 2 false=Geometry.b1563 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1563
  · have he : Geometry.b1112.half 2 true=Geometry.b1564 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1564

theorem bound1111 : BoxMajorant Geometry.b1111 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1111.Widths)
  · have he : Geometry.b1111.half 2 false=Geometry.b1561 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1561
  · have he : Geometry.b1111.half 2 true=Geometry.b1562 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1562

theorem bound807 : BoxMajorant Geometry.b807 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b807.Widths)
  · have he : Geometry.b807.half 1 false=Geometry.b1111 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1111
  · have he : Geometry.b807.half 1 true=Geometry.b1112 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1112

end N7.Kernel.Cover
