import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0310
import N7.Kernel.PositiveGroups.G0365
import N7.Kernel.PositiveGroups.G0396
import N7.Kernel.PositiveGroups.G0397
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5482 : BoxMajorant Geometry.b5482 := by
  exact PositiveLeaves.L1509.bound

theorem bound5481 : BoxMajorant Geometry.b5481 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5481 2 (by decide +kernel) x hx hd ho).elim

theorem bound5350 : BoxMajorant Geometry.b5350 := by
  exact PositiveLeaves.L1508.bound

theorem bound5349 : BoxMajorant Geometry.b5349 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5349.Widths)
  · have he : Geometry.b5349.half 2 false=Geometry.b5481 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5481
  · have he : Geometry.b5349.half 2 true=Geometry.b5482 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5482

theorem bound5232 : BoxMajorant Geometry.b5232 := by
  exact PositiveLeaves.L1507.bound

theorem bound5231 : BoxMajorant Geometry.b5231 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5231.Widths)
  · have he : Geometry.b5231.half 1 false=Geometry.b5349 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5349
  · have he : Geometry.b5231.half 1 true=Geometry.b5350 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5350

theorem bound5006 : BoxMajorant Geometry.b5006 := by
  exact PositiveLeaves.L1505.bound

theorem bound5005 : BoxMajorant Geometry.b5005 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5005 2 (by decide +kernel) x hx hd ho).elim

theorem bound5004 : BoxMajorant Geometry.b5004 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5004.Widths)
  · have he : Geometry.b5004.half 0 false=Geometry.b5231 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5231
  · have he : Geometry.b5004.half 0 true=Geometry.b5232 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5232

theorem bound5003 : BoxMajorant Geometry.b5003 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5003 2 (by decide +kernel) x hx hd ho).elim

theorem bound4644 : BoxMajorant Geometry.b4644 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4644.Widths)
  · have he : Geometry.b4644.half 2 false=Geometry.b5005 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5005
  · have he : Geometry.b4644.half 2 true=Geometry.b5006 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5006

theorem bound4643 : BoxMajorant Geometry.b4643 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4643.Widths)
  · have he : Geometry.b4643.half 2 false=Geometry.b5003 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5003
  · have he : Geometry.b4643.half 2 true=Geometry.b5004 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5004

theorem bound4382 : BoxMajorant Geometry.b4382 := by
  exact PositiveLeaves.L1504.bound

theorem bound4381 : BoxMajorant Geometry.b4381 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4381.Widths)
  · have he : Geometry.b4381.half 1 false=Geometry.b4643 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4643
  · have he : Geometry.b4381.half 1 true=Geometry.b4644 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4644

theorem bound4036 : BoxMajorant Geometry.b4036 := by
  exact PositiveLeaves.L1503.bound

theorem bound4035 : BoxMajorant Geometry.b4035 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4035.Widths)
  · have he : Geometry.b4035.half 0 false=Geometry.b4381 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4381
  · have he : Geometry.b4035.half 0 true=Geometry.b4382 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4382

theorem bound3648 : BoxMajorant Geometry.b3648 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3648.Widths)
  · have he : Geometry.b3648.half 2 false=Geometry.b4035 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4035
  · have he : Geometry.b3648.half 2 true=Geometry.b4036 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4036

end N7.Kernel.Cover
