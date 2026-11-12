import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.PositiveGroups.G0381
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4218 : BoxMajorant Geometry.b4218 := by
  exact PositiveLeaves.L2116.bound

theorem bound4217 : BoxMajorant Geometry.b4217 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4217 2 (by decide +kernel) x hx hd ho).elim

theorem bound4216 : BoxMajorant Geometry.b4216 := by
  exact PositiveLeaves.L2119.bound

theorem bound4215 : BoxMajorant Geometry.b4215 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4215 2 (by decide +kernel) x hx hd ho).elim

theorem bound3842 : BoxMajorant Geometry.b3842 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3842.Widths)
  · have he : Geometry.b3842.half 0 false=Geometry.b4217 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4217
  · have he : Geometry.b3842.half 0 true=Geometry.b4218 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4218

theorem bound3841 : BoxMajorant Geometry.b3841 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3841 2 (by decide +kernel) x hx hd ho).elim

theorem bound3840 : BoxMajorant Geometry.b3840 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3840.Widths)
  · have he : Geometry.b3840.half 0 false=Geometry.b4215 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4215
  · have he : Geometry.b3840.half 0 true=Geometry.b4216 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4216

theorem bound3839 : BoxMajorant Geometry.b3839 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3839 2 (by decide +kernel) x hx hd ho).elim

theorem bound3534 : BoxMajorant Geometry.b3534 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3534.Widths)
  · have he : Geometry.b3534.half 2 false=Geometry.b3841 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3841
  · have he : Geometry.b3534.half 2 true=Geometry.b3842 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3842

theorem bound3533 : BoxMajorant Geometry.b3533 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3533.Widths)
  · have he : Geometry.b3533.half 2 false=Geometry.b3839 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3839
  · have he : Geometry.b3533.half 2 true=Geometry.b3840 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3840

theorem bound3260 : BoxMajorant Geometry.b3260 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3260.Widths)
  · have he : Geometry.b3260.half 1 false=Geometry.b3533 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3533
  · have he : Geometry.b3260.half 1 true=Geometry.b3534 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3534

theorem bound3259 : BoxMajorant Geometry.b3259 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3259 2 (by decide +kernel) x hx hd ho).elim

theorem bound2933 : BoxMajorant Geometry.b2933 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2933.Widths)
  · have he : Geometry.b2933.half 0 false=Geometry.b3259 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3259
  · have he : Geometry.b2933.half 0 true=Geometry.b3260 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3260

end N7.Kernel.Cover
