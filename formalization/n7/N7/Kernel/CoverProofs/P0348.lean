import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.PositiveGroups.G0408
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4762 : BoxMajorant Geometry.b4762 := by
  exact PositiveLeaves.L2776.bound

theorem bound4761 : BoxMajorant Geometry.b4761 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4761 2 (by decide +kernel) x hx hd ho).elim

theorem bound4473 : BoxMajorant Geometry.b4473 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4473.Widths)
  · have he : Geometry.b4473.half 2 false=Geometry.b4761 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4761
  · have he : Geometry.b4473.half 2 true=Geometry.b4762 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4762

end N7.Kernel.Cover
