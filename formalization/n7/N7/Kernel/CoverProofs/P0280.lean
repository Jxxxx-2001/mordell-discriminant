import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.PositiveGroups.G0334
import N7.Kernel.PositiveGroups.G0364
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4398 : BoxMajorant Geometry.b4398 := by
  exact PositiveLeaves.L1452.bound

theorem bound4397 : BoxMajorant Geometry.b4397 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4397 2 (by decide +kernel) x hx hd ho).elim

theorem bound4048 : BoxMajorant Geometry.b4048 := by
  exact PositiveLeaves.L1451.bound

theorem bound4047 : BoxMajorant Geometry.b4047 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4047.Widths)
  · have he : Geometry.b4047.half 0 false=Geometry.b4397 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4397
  · have he : Geometry.b4047.half 0 true=Geometry.b4398 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4398

theorem bound3654 : BoxMajorant Geometry.b3654 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3654.Widths)
  · have he : Geometry.b3654.half 2 false=Geometry.b4047 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4047
  · have he : Geometry.b3654.half 2 true=Geometry.b4048 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4048

end N7.Kernel.Cover
