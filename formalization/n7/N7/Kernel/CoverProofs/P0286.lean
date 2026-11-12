import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.PositiveGroups.G0259
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4056 : BoxMajorant Geometry.b4056 := by
  exact PositiveLeaves.L1370.bound

theorem bound4055 : BoxMajorant Geometry.b4055 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4055 2 (by decide +kernel) x hx hd ho).elim

theorem bound3658 : BoxMajorant Geometry.b3658 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3658.Widths)
  · have he : Geometry.b3658.half 2 false=Geometry.b4055 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4055
  · have he : Geometry.b3658.half 2 true=Geometry.b4056 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4056

end N7.Kernel.Cover
