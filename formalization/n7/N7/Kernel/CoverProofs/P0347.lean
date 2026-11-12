import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.PositiveGroups.G0425
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5138 : BoxMajorant Geometry.b5138 := by
  exact PositiveLeaves.L2778.bound

theorem bound5137 : BoxMajorant Geometry.b5137 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5137 2 (by decide +kernel) x hx hd ho).elim

theorem bound4760 : BoxMajorant Geometry.b4760 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4760.Widths)
  · have he : Geometry.b4760.half 0 false=Geometry.b5137 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5137
  · have he : Geometry.b4760.half 0 true=Geometry.b5138 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5138

theorem bound4759 : BoxMajorant Geometry.b4759 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4759 2 (by decide +kernel) x hx hd ho).elim

theorem bound4472 : BoxMajorant Geometry.b4472 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4472.Widths)
  · have he : Geometry.b4472.half 2 false=Geometry.b4759 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4759
  · have he : Geometry.b4472.half 2 true=Geometry.b4760 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4760

end N7.Kernel.Cover
