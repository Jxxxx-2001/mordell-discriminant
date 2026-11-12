import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.PositiveGroups.G0344
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4884 : BoxMajorant Geometry.b4884 := by
  exact PositiveLeaves.L1865.bound

theorem bound4883 : BoxMajorant Geometry.b4883 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4883 2 (by decide +kernel) x hx hd ho).elim

theorem bound4562 : BoxMajorant Geometry.b4562 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4562.Widths)
  · have he : Geometry.b4562.half 2 false=Geometry.b4883 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4883
  · have he : Geometry.b4562.half 2 true=Geometry.b4884 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4884

theorem bound4561 : BoxMajorant Geometry.b4561 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4561 2 (by decide +kernel) x hx hd ho).elim

theorem bound4288 : BoxMajorant Geometry.b4288 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4288.Widths)
  · have he : Geometry.b4288.half 1 false=Geometry.b4561 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4561
  · have he : Geometry.b4288.half 1 true=Geometry.b4562 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4562

theorem bound4287 : BoxMajorant Geometry.b4287 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4287 2 (by decide +kernel) x hx hd ho).elim

theorem bound3924 : BoxMajorant Geometry.b3924 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3924.Widths)
  · have he : Geometry.b3924.half 0 false=Geometry.b4287 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4287
  · have he : Geometry.b3924.half 0 true=Geometry.b4288 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4288

theorem bound3923 : BoxMajorant Geometry.b3923 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3923 2 (by decide +kernel) x hx hd ho).elim

theorem bound3582 : BoxMajorant Geometry.b3582 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3582.Widths)
  · have he : Geometry.b3582.half 2 false=Geometry.b3923 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3923
  · have he : Geometry.b3582.half 2 true=Geometry.b3924 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3924

theorem bound3581 : BoxMajorant Geometry.b3581 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3581 2 (by decide +kernel) x hx hd ho).elim

theorem bound3312 : BoxMajorant Geometry.b3312 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3312.Widths)
  · have he : Geometry.b3312.half 1 false=Geometry.b3581 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3581
  · have he : Geometry.b3312.half 1 true=Geometry.b3582 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3582

theorem bound3311 : BoxMajorant Geometry.b3311 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3311 2 (by decide +kernel) x hx hd ho).elim

theorem bound2976 : BoxMajorant Geometry.b2976 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2976.Widths)
  · have he : Geometry.b2976.half 0 false=Geometry.b3311 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3311
  · have he : Geometry.b2976.half 0 true=Geometry.b3312 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3312

theorem bound2975 : BoxMajorant Geometry.b2975 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2975 2 (by decide +kernel) x hx hd ho).elim

theorem bound2602 : BoxMajorant Geometry.b2602 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2602.Widths)
  · have he : Geometry.b2602.half 2 false=Geometry.b2975 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2975
  · have he : Geometry.b2602.half 2 true=Geometry.b2976 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2976

end N7.Kernel.Cover
