import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.PositiveGroups.G0328
import N7.Kernel.PositiveGroups.G0329
import N7.Kernel.PositiveGroups.G0356
import N7.Kernel.PositiveGroups.G0357
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4080 : BoxMajorant Geometry.b4080 := by
  exact PositiveLeaves.L969.bound

theorem bound4079 : BoxMajorant Geometry.b4079 := by
  exact PositiveLeaves.L970.bound

theorem bound4078 : BoxMajorant Geometry.b4078 := by
  exact PositiveLeaves.L972.bound

theorem bound4077 : BoxMajorant Geometry.b4077 := by
  exact PositiveLeaves.L973.bound

theorem bound3678 : BoxMajorant Geometry.b3678 := by
  exact PositiveLeaves.L968.bound

theorem bound3677 : BoxMajorant Geometry.b3677 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3677.Widths)
  · have he : Geometry.b3677.half 2 false=Geometry.b4079 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4079
  · have he : Geometry.b3677.half 2 true=Geometry.b4080 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4080

theorem bound3676 : BoxMajorant Geometry.b3676 := by
  exact PositiveLeaves.L971.bound

theorem bound3675 : BoxMajorant Geometry.b3675 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3675.Widths)
  · have he : Geometry.b3675.half 2 false=Geometry.b4077 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4077
  · have he : Geometry.b3675.half 2 true=Geometry.b4078 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4078

theorem bound3410 : BoxMajorant Geometry.b3410 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3410.Widths)
  · have he : Geometry.b3410.half 1 false=Geometry.b3677 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3677
  · have he : Geometry.b3410.half 1 true=Geometry.b3678 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3678

theorem bound3409 : BoxMajorant Geometry.b3409 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3409.Widths)
  · have he : Geometry.b3409.half 1 false=Geometry.b3675 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3675
  · have he : Geometry.b3409.half 1 true=Geometry.b3676 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3676

theorem bound3077 : BoxMajorant Geometry.b3077 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3077.Widths)
  · have he : Geometry.b3077.half 0 false=Geometry.b3409 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3409
  · have he : Geometry.b3077.half 0 true=Geometry.b3410 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3410

end N7.Kernel.Cover
