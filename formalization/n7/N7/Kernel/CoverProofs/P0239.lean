import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.PositiveGroups.G0264
import N7.Kernel.PositiveGroups.G0291
import N7.Kernel.PositiveGroups.G0314
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3922 : BoxMajorant Geometry.b3922 := by
  exact PositiveLeaves.L1877.bound

theorem bound3921 : BoxMajorant Geometry.b3921 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3921 2 (by decide +kernel) x hx hd ho).elim

theorem bound3580 : BoxMajorant Geometry.b3580 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3580.Widths)
  · have he : Geometry.b3580.half 2 false=Geometry.b3921 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3921
  · have he : Geometry.b3580.half 2 true=Geometry.b3922 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3922

theorem bound3579 : BoxMajorant Geometry.b3579 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3579 2 (by decide +kernel) x hx hd ho).elim

theorem bound3310 : BoxMajorant Geometry.b3310 := by
  exact PositiveLeaves.L1876.bound

theorem bound3309 : BoxMajorant Geometry.b3309 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3309.Widths)
  · have he : Geometry.b3309.half 1 false=Geometry.b3579 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3579
  · have he : Geometry.b3309.half 1 true=Geometry.b3580 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3580

theorem bound2974 : BoxMajorant Geometry.b2974 := by
  exact PositiveLeaves.L1875.bound

theorem bound2973 : BoxMajorant Geometry.b2973 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2973.Widths)
  · have he : Geometry.b2973.half 0 false=Geometry.b3309 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3309
  · have he : Geometry.b2973.half 0 true=Geometry.b3310 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3310

theorem bound2600 : BoxMajorant Geometry.b2600 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2600.Widths)
  · have he : Geometry.b2600.half 2 false=Geometry.b2973 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2973
  · have he : Geometry.b2600.half 2 true=Geometry.b2974 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2974

end N7.Kernel.Cover
