import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.PositiveGroups.G0070
import N7.Kernel.PositiveGroups.G0071
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1594 : BoxMajorant Geometry.b1594 := by
  exact PositiveLeaves.L2241.bound

theorem bound1593 : BoxMajorant Geometry.b1593 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1593 2 (by decide +kernel) x hx hd ho).elim

theorem bound1592 : BoxMajorant Geometry.b1592 := by
  exact PositiveLeaves.L2243.bound

theorem bound1591 : BoxMajorant Geometry.b1591 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1591 2 (by decide +kernel) x hx hd ho).elim

theorem bound1132 : BoxMajorant Geometry.b1132 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1132.Widths)
  · have he : Geometry.b1132.half 2 false=Geometry.b1593 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1593
  · have he : Geometry.b1132.half 2 true=Geometry.b1594 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1594

theorem bound1131 : BoxMajorant Geometry.b1131 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1131.Widths)
  · have he : Geometry.b1131.half 2 false=Geometry.b1591 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1591
  · have he : Geometry.b1131.half 2 true=Geometry.b1592 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1592

theorem bound822 : BoxMajorant Geometry.b822 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b822.Widths)
  · have he : Geometry.b822.half 1 false=Geometry.b1131 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1131
  · have he : Geometry.b822.half 1 true=Geometry.b1132 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1132

theorem bound821 : BoxMajorant Geometry.b821 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b821 2 (by decide +kernel) x hx hd ho).elim

theorem bound541 : BoxMajorant Geometry.b541 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b541.Widths)
  · have he : Geometry.b541.half 0 false=Geometry.b821 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound821
  · have he : Geometry.b541.half 0 true=Geometry.b822 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound822

end N7.Kernel.Cover
