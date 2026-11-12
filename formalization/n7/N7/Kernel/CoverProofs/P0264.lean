import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.PositiveGroups.G0261
import N7.Kernel.PositiveGroups.G0287
import N7.Kernel.PositiveGroups.G0311
import N7.Kernel.PositiveGroups.G0336
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4028 : BoxMajorant Geometry.b4028 := by
  exact PositiveLeaves.L1551.bound

theorem bound4027 : BoxMajorant Geometry.b4027 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4027 2 (by decide +kernel) x hx hd ho).elim

theorem bound3644 : BoxMajorant Geometry.b3644 := by
  exact PositiveLeaves.L1550.bound

theorem bound3643 : BoxMajorant Geometry.b3643 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3643.Widths)
  · have he : Geometry.b3643.half 2 false=Geometry.b4027 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4027
  · have he : Geometry.b3643.half 2 true=Geometry.b4028 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4028

theorem bound3368 : BoxMajorant Geometry.b3368 := by
  exact PositiveLeaves.L1549.bound

theorem bound3367 : BoxMajorant Geometry.b3367 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3367.Widths)
  · have he : Geometry.b3367.half 1 false=Geometry.b3643 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3643
  · have he : Geometry.b3367.half 1 true=Geometry.b3644 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3644

theorem bound3026 : BoxMajorant Geometry.b3026 := by
  exact PositiveLeaves.L1548.bound

theorem bound3025 : BoxMajorant Geometry.b3025 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3025.Widths)
  · have he : Geometry.b3025.half 0 false=Geometry.b3367 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3367
  · have he : Geometry.b3025.half 0 true=Geometry.b3368 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3368

theorem bound2627 : BoxMajorant Geometry.b2627 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2627.Widths)
  · have he : Geometry.b2627.half 2 false=Geometry.b3025 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3025
  · have he : Geometry.b2627.half 2 true=Geometry.b3026 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3026

end N7.Kernel.Cover
