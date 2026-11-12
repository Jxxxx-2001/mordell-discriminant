import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.PositiveGroups.G0047
import N7.Kernel.PositiveGroups.G0048
import N7.Kernel.PositiveGroups.G0110
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1542 : BoxMajorant Geometry.b1542 := by
  exact PositiveLeaves.L2397.bound

theorem bound1541 : BoxMajorant Geometry.b1541 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1541 2 (by decide +kernel) x hx hd ho).elim

theorem bound1540 : BoxMajorant Geometry.b1540 := by
  exact PositiveLeaves.L2399.bound

theorem bound1539 : BoxMajorant Geometry.b1539 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1539 2 (by decide +kernel) x hx hd ho).elim

theorem bound1538 : BoxMajorant Geometry.b1538 := by
  exact PositiveLeaves.L2401.bound

theorem bound1537 : BoxMajorant Geometry.b1537 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1537 2 (by decide +kernel) x hx hd ho).elim

theorem bound1096 : BoxMajorant Geometry.b1096 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1096.Widths)
  · have he : Geometry.b1096.half 2 false=Geometry.b1541 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1541
  · have he : Geometry.b1096.half 2 true=Geometry.b1542 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1542

theorem bound1095 : BoxMajorant Geometry.b1095 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1095.Widths)
  · have he : Geometry.b1095.half 2 false=Geometry.b1539 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1539
  · have he : Geometry.b1095.half 2 true=Geometry.b1540 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1540

theorem bound1094 : BoxMajorant Geometry.b1094 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1094.Widths)
  · have he : Geometry.b1094.half 2 false=Geometry.b1537 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1537
  · have he : Geometry.b1094.half 2 true=Geometry.b1538 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1538

theorem bound1093 : BoxMajorant Geometry.b1093 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1093 2 (by decide +kernel) x hx hd ho).elim

theorem bound794 : BoxMajorant Geometry.b794 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b794.Widths)
  · have he : Geometry.b794.half 1 false=Geometry.b1095 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1095
  · have he : Geometry.b794.half 1 true=Geometry.b1096 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1096

theorem bound793 : BoxMajorant Geometry.b793 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b793.Widths)
  · have he : Geometry.b793.half 1 false=Geometry.b1093 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1093
  · have he : Geometry.b793.half 1 true=Geometry.b1094 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1094

theorem bound511 : BoxMajorant Geometry.b511 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b511.Widths)
  · have he : Geometry.b511.half 0 false=Geometry.b793 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound793
  · have he : Geometry.b511.half 0 true=Geometry.b794 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound794

end N7.Kernel.Cover
