import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.PositiveGroups.G0012
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1490 : BoxMajorant Geometry.b1490 := by
  exact PositiveLeaves.L2539.bound

theorem bound1489 : BoxMajorant Geometry.b1489 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1489 2 (by decide +kernel) x hx hd ho).elim

theorem bound1060 : BoxMajorant Geometry.b1060 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1060.Widths)
  · have he : Geometry.b1060.half 2 false=Geometry.b1489 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1489
  · have he : Geometry.b1060.half 2 true=Geometry.b1490 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1490

theorem bound1059 : BoxMajorant Geometry.b1059 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1059 2 (by decide +kernel) x hx hd ho).elim

theorem bound768 : BoxMajorant Geometry.b768 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b768.Widths)
  · have he : Geometry.b768.half 1 false=Geometry.b1059 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1059
  · have he : Geometry.b768.half 1 true=Geometry.b1060 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1060

theorem bound767 : BoxMajorant Geometry.b767 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b767 2 (by decide +kernel) x hx hd ho).elim

theorem bound492 : BoxMajorant Geometry.b492 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b492.Widths)
  · have he : Geometry.b492.half 0 false=Geometry.b767 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound767
  · have he : Geometry.b492.half 0 true=Geometry.b768 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound768

end N7.Kernel.Cover
