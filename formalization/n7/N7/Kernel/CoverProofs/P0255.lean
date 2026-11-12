import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.PositiveGroups.G0261
import N7.Kernel.PositiveGroups.G0288
import N7.Kernel.PositiveGroups.G0338
import N7.Kernel.PositiveGroups.G0368
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3994 : BoxMajorant Geometry.b3994 := by
  exact PositiveLeaves.L1633.bound

theorem bound3993 : BoxMajorant Geometry.b3993 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3993 2 (by decide +kernel) x hx hd ho).elim

theorem bound3624 : BoxMajorant Geometry.b3624 := by
  exact PositiveLeaves.L1632.bound

theorem bound3623 : BoxMajorant Geometry.b3623 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3623.Widths)
  · have he : Geometry.b3623.half 2 false=Geometry.b3993 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3993
  · have he : Geometry.b3623.half 2 true=Geometry.b3994 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3994

theorem bound3350 : BoxMajorant Geometry.b3350 := by
  exact PositiveLeaves.L1631.bound

theorem bound3349 : BoxMajorant Geometry.b3349 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3349.Widths)
  · have he : Geometry.b3349.half 1 false=Geometry.b3623 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3623
  · have he : Geometry.b3349.half 1 true=Geometry.b3624 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3624

theorem bound3008 : BoxMajorant Geometry.b3008 := by
  exact PositiveLeaves.L1630.bound

theorem bound3007 : BoxMajorant Geometry.b3007 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3007.Widths)
  · have he : Geometry.b3007.half 0 false=Geometry.b3349 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3349
  · have he : Geometry.b3007.half 0 true=Geometry.b3350 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3350

theorem bound2618 : BoxMajorant Geometry.b2618 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2618.Widths)
  · have he : Geometry.b2618.half 2 false=Geometry.b3007 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3007
  · have he : Geometry.b2618.half 2 true=Geometry.b3008 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3008

end N7.Kernel.Cover
