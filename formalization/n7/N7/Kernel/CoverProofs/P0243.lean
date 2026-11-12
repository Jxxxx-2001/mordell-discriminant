import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.PositiveGroups.G0263
import N7.Kernel.PositiveGroups.G0290
import N7.Kernel.PositiveGroups.G0344
import N7.Kernel.PositiveGroups.G0375
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4290 : BoxMajorant Geometry.b4290 := by
  exact PositiveLeaves.L1848.bound

theorem bound4289 : BoxMajorant Geometry.b4289 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4289 2 (by decide +kernel) x hx hd ho).elim

theorem bound3936 : BoxMajorant Geometry.b3936 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3936.Widths)
  · have he : Geometry.b3936.half 0 false=Geometry.b4289 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4289
  · have he : Geometry.b3936.half 0 true=Geometry.b4290 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4290

theorem bound3935 : BoxMajorant Geometry.b3935 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3935 2 (by decide +kernel) x hx hd ho).elim

theorem bound3934 : BoxMajorant Geometry.b3934 := by
  exact PositiveLeaves.L1851.bound

theorem bound3933 : BoxMajorant Geometry.b3933 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3933 2 (by decide +kernel) x hx hd ho).elim

theorem bound3588 : BoxMajorant Geometry.b3588 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3588.Widths)
  · have he : Geometry.b3588.half 2 false=Geometry.b3935 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3935
  · have he : Geometry.b3588.half 2 true=Geometry.b3936 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3936

theorem bound3587 : BoxMajorant Geometry.b3587 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3587.Widths)
  · have he : Geometry.b3587.half 2 false=Geometry.b3933 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3933
  · have he : Geometry.b3587.half 2 true=Geometry.b3934 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3934

theorem bound3318 : BoxMajorant Geometry.b3318 := by
  exact PositiveLeaves.L1847.bound

theorem bound3317 : BoxMajorant Geometry.b3317 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3317.Widths)
  · have he : Geometry.b3317.half 1 false=Geometry.b3587 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3587
  · have he : Geometry.b3317.half 1 true=Geometry.b3588 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3588

theorem bound2982 : BoxMajorant Geometry.b2982 := by
  exact PositiveLeaves.L1846.bound

theorem bound2981 : BoxMajorant Geometry.b2981 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2981.Widths)
  · have he : Geometry.b2981.half 0 false=Geometry.b3317 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3317
  · have he : Geometry.b2981.half 0 true=Geometry.b3318 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3318

theorem bound2605 : BoxMajorant Geometry.b2605 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2605.Widths)
  · have he : Geometry.b2605.half 2 false=Geometry.b2981 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2981
  · have he : Geometry.b2605.half 2 true=Geometry.b2982 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2982

end N7.Kernel.Cover
