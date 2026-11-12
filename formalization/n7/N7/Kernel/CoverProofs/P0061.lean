import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.PositiveGroups.G0019
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1582 : BoxMajorant Geometry.b1582 := by
  exact PositiveLeaves.L2266.bound

theorem bound1581 : BoxMajorant Geometry.b1581 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1581 2 (by decide +kernel) x hx hd ho).elim

theorem bound1124 : BoxMajorant Geometry.b1124 := by
  exact PositiveLeaves.L2265.bound

theorem bound1123 : BoxMajorant Geometry.b1123 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1123.Widths)
  · have he : Geometry.b1123.half 2 false=Geometry.b1581 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1581
  · have he : Geometry.b1123.half 2 true=Geometry.b1582 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1582

theorem bound814 : BoxMajorant Geometry.b814 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b814.Widths)
  · have he : Geometry.b814.half 1 false=Geometry.b1123 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1123
  · have he : Geometry.b814.half 1 true=Geometry.b1124 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1124

end N7.Kernel.Cover
