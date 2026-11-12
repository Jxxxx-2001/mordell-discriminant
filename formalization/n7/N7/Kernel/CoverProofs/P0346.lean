import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.PositiveGroups.G0408
import N7.Kernel.PositiveGroups.G0424
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5136 : BoxMajorant Geometry.b5136 := by
  exact PositiveLeaves.L2785.bound

theorem bound5135 : BoxMajorant Geometry.b5135 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5135 2 (by decide +kernel) x hx hd ho).elim

theorem bound4758 : BoxMajorant Geometry.b4758 := by
  exact PositiveLeaves.L2784.bound

theorem bound4757 : BoxMajorant Geometry.b4757 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4757.Widths)
  · have he : Geometry.b4757.half 0 false=Geometry.b5135 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5135
  · have he : Geometry.b4757.half 0 true=Geometry.b5136 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5136

theorem bound4469 : BoxMajorant Geometry.b4469 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4469.Widths)
  · have he : Geometry.b4469.half 2 false=Geometry.b4757 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4757
  · have he : Geometry.b4469.half 2 true=Geometry.b4758 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4758

end N7.Kernel.Cover
