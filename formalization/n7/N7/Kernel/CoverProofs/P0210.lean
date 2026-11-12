import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.PositiveGroups.G0184
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3810 : BoxMajorant Geometry.b3810 := by
  exact PositiveLeaves.L2485.bound

theorem bound3809 : BoxMajorant Geometry.b3809 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3809 2 (by decide +kernel) x hx hd ho).elim

theorem bound3808 : BoxMajorant Geometry.b3808 := by
  exact PositiveLeaves.L2487.bound

theorem bound3807 : BoxMajorant Geometry.b3807 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3807 2 (by decide +kernel) x hx hd ho).elim

theorem bound3510 : BoxMajorant Geometry.b3510 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3510.Widths)
  · have he : Geometry.b3510.half 2 false=Geometry.b3809 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3809
  · have he : Geometry.b3510.half 2 true=Geometry.b3810 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3810

theorem bound3509 : BoxMajorant Geometry.b3509 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3509.Widths)
  · have he : Geometry.b3509.half 2 false=Geometry.b3807 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3807
  · have he : Geometry.b3509.half 2 true=Geometry.b3808 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3808

theorem bound3226 : BoxMajorant Geometry.b3226 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3226.Widths)
  · have he : Geometry.b3226.half 1 false=Geometry.b3509 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3509
  · have he : Geometry.b3226.half 1 true=Geometry.b3510 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3510

end N7.Kernel.Cover
