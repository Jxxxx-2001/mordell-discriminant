import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.PositiveGroups.G0024
import N7.Kernel.PositiveGroups.G0072
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1500 : BoxMajorant Geometry.b1500 := by
  exact PositiveLeaves.L2523.bound

theorem bound1499 : BoxMajorant Geometry.b1499 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1499 2 (by decide +kernel) x hx hd ho).elim

theorem bound1498 : BoxMajorant Geometry.b1498 := by
  exact PositiveLeaves.L2525.bound

theorem bound1497 : BoxMajorant Geometry.b1497 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1497 2 (by decide +kernel) x hx hd ho).elim

theorem bound1066 : BoxMajorant Geometry.b1066 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1066.Widths)
  · have he : Geometry.b1066.half 2 false=Geometry.b1499 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1499
  · have he : Geometry.b1066.half 2 true=Geometry.b1500 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1500

theorem bound1065 : BoxMajorant Geometry.b1065 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1065.Widths)
  · have he : Geometry.b1065.half 2 false=Geometry.b1497 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1497
  · have he : Geometry.b1065.half 2 true=Geometry.b1498 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1498

theorem bound772 : BoxMajorant Geometry.b772 := by
  exact PositiveLeaves.L2522.bound

theorem bound771 : BoxMajorant Geometry.b771 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b771.Widths)
  · have he : Geometry.b771.half 1 false=Geometry.b1065 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1065
  · have he : Geometry.b771.half 1 true=Geometry.b1066 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1066

theorem bound496 : BoxMajorant Geometry.b496 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b496.Widths)
  · have he : Geometry.b496.half 0 false=Geometry.b771 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound771
  · have he : Geometry.b496.half 0 true=Geometry.b772 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound772

end N7.Kernel.Cover
