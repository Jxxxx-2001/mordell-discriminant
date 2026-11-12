import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.PositiveGroups.G0301
import N7.Kernel.PositiveGroups.G0324
import N7.Kernel.PositiveGroups.G0355
import N7.Kernel.PositiveGroups.G0388
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4096 : BoxMajorant Geometry.b4096 := by
  exact PositiveLeaves.L659.bound

theorem bound4095 : BoxMajorant Geometry.b4095 := by
  exact PositiveLeaves.L660.bound

theorem bound3694 : BoxMajorant Geometry.b3694 := by
  exact PositiveLeaves.L658.bound

theorem bound3693 : BoxMajorant Geometry.b3693 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3693.Widths)
  · have he : Geometry.b3693.half 2 false=Geometry.b4095 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4095
  · have he : Geometry.b3693.half 2 true=Geometry.b4096 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4096

theorem bound3426 : BoxMajorant Geometry.b3426 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3426.Widths)
  · have he : Geometry.b3426.half 1 false=Geometry.b3693 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3693
  · have he : Geometry.b3426.half 1 true=Geometry.b3694 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3694

theorem bound3425 : BoxMajorant Geometry.b3425 := by
  exact PositiveLeaves.L661.bound

theorem bound3136 : BoxMajorant Geometry.b3136 := by
  exact PositiveLeaves.L657.bound

theorem bound3135 : BoxMajorant Geometry.b3135 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3135.Widths)
  · have he : Geometry.b3135.half 0 false=Geometry.b3425 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3425
  · have he : Geometry.b3135.half 0 true=Geometry.b3426 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3426

theorem bound2740 : BoxMajorant Geometry.b2740 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2740.Widths)
  · have he : Geometry.b2740.half 2 false=Geometry.b3135 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3135
  · have he : Geometry.b2740.half 2 true=Geometry.b3136 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3136

end N7.Kernel.Cover
