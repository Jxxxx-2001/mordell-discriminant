import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.PositiveGroups.G0295
import N7.Kernel.PositiveGroups.G0318
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3830 : BoxMajorant Geometry.b3830 := by
  exact PositiveLeaves.L2141.bound

theorem bound3829 : BoxMajorant Geometry.b3829 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3829 2 (by decide +kernel) x hx hd ho).elim

theorem bound3828 : BoxMajorant Geometry.b3828 := by
  exact PositiveLeaves.L2143.bound

theorem bound3827 : BoxMajorant Geometry.b3827 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3827 2 (by decide +kernel) x hx hd ho).elim

theorem bound3526 : BoxMajorant Geometry.b3526 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3526.Widths)
  · have he : Geometry.b3526.half 2 false=Geometry.b3829 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3829
  · have he : Geometry.b3526.half 2 true=Geometry.b3830 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3830

theorem bound3525 : BoxMajorant Geometry.b3525 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3525.Widths)
  · have he : Geometry.b3525.half 2 false=Geometry.b3827 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3827
  · have he : Geometry.b3525.half 2 true=Geometry.b3828 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3828

theorem bound3252 : BoxMajorant Geometry.b3252 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3252.Widths)
  · have he : Geometry.b3252.half 1 false=Geometry.b3525 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3525
  · have he : Geometry.b3252.half 1 true=Geometry.b3526 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3526

theorem bound3251 : BoxMajorant Geometry.b3251 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3251 2 (by decide +kernel) x hx hd ho).elim

theorem bound2928 : BoxMajorant Geometry.b2928 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2928.Widths)
  · have he : Geometry.b2928.half 0 false=Geometry.b3251 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3251
  · have he : Geometry.b2928.half 0 true=Geometry.b3252 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3252

end N7.Kernel.Cover
