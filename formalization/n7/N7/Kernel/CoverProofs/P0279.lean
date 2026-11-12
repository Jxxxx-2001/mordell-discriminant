import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.PositiveGroups.G0334
import N7.Kernel.PositiveGroups.G0395
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5028 : BoxMajorant Geometry.b5028 := by
  exact PositiveLeaves.L1456.bound

theorem bound5027 : BoxMajorant Geometry.b5027 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5027 2 (by decide +kernel) x hx hd ho).elim

theorem bound4658 : BoxMajorant Geometry.b4658 := by
  exact PositiveLeaves.L1455.bound

theorem bound4657 : BoxMajorant Geometry.b4657 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4657.Widths)
  · have he : Geometry.b4657.half 2 false=Geometry.b5027 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5027
  · have he : Geometry.b4657.half 2 true=Geometry.b5028 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5028

theorem bound4396 : BoxMajorant Geometry.b4396 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4396.Widths)
  · have he : Geometry.b4396.half 1 false=Geometry.b4657 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4657
  · have he : Geometry.b4396.half 1 true=Geometry.b4658 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4658

theorem bound4395 : BoxMajorant Geometry.b4395 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4395 2 (by decide +kernel) x hx hd ho).elim

theorem bound4046 : BoxMajorant Geometry.b4046 := by
  exact PositiveLeaves.L1454.bound

theorem bound4045 : BoxMajorant Geometry.b4045 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4045.Widths)
  · have he : Geometry.b4045.half 0 false=Geometry.b4395 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4395
  · have he : Geometry.b4045.half 0 true=Geometry.b4396 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4396

theorem bound3653 : BoxMajorant Geometry.b3653 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3653.Widths)
  · have he : Geometry.b3653.half 2 false=Geometry.b4045 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4045
  · have he : Geometry.b3653.half 2 true=Geometry.b4046 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4046

end N7.Kernel.Cover
