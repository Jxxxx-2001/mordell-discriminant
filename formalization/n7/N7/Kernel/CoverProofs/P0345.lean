import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.PositiveGroups.G0384
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4756 : BoxMajorant Geometry.b4756 := by
  exact PositiveLeaves.L2787.bound

theorem bound4755 : BoxMajorant Geometry.b4755 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4755 2 (by decide +kernel) x hx hd ho).elim

theorem bound4468 : BoxMajorant Geometry.b4468 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4468.Widths)
  · have he : Geometry.b4468.half 2 false=Geometry.b4755 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4755
  · have he : Geometry.b4468.half 2 true=Geometry.b4756 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4756

end N7.Kernel.Cover
