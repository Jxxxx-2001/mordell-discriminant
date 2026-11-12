import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0441
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5406 : BoxMajorant Geometry.b5406 := by
  exact PositiveLeaves.L2893.bound

theorem bound5405 : BoxMajorant Geometry.b5405 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5405 2 (by decide +kernel) x hx hd ho).elim

theorem bound5283 : BoxMajorant Geometry.b5283 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5283.Widths)
  · have he : Geometry.b5283.half 2 false=Geometry.b5405 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5405
  · have he : Geometry.b5283.half 2 true=Geometry.b5406 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5406

end N7.Kernel.Cover
