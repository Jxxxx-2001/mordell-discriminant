import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0419
import N7.Kernel.PositiveGroups.G0436
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5478 : BoxMajorant Geometry.b5478 := by
  exact PositiveLeaves.L1769.bound

theorem bound5477 : BoxMajorant Geometry.b5477 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5477 2 (by decide +kernel) x hx hd ho).elim

theorem bound5346 : BoxMajorant Geometry.b5346 := by
  exact PositiveLeaves.L1768.bound

theorem bound5345 : BoxMajorant Geometry.b5345 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5345.Widths)
  · have he : Geometry.b5345.half 2 false=Geometry.b5477 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5477
  · have he : Geometry.b5345.half 2 true=Geometry.b5478 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5478

theorem bound5186 : BoxMajorant Geometry.b5186 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5186.Widths)
  · have he : Geometry.b5186.half 1 false=Geometry.b5345 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5345
  · have he : Geometry.b5186.half 1 true=Geometry.b5346 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5346

theorem bound5185 : BoxMajorant Geometry.b5185 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5185 2 (by decide +kernel) x hx hd ho).elim

theorem bound4910 : BoxMajorant Geometry.b4910 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4910.Widths)
  · have he : Geometry.b4910.half 0 false=Geometry.b5185 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5185
  · have he : Geometry.b4910.half 0 true=Geometry.b5186 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5186

theorem bound4909 : BoxMajorant Geometry.b4909 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4909 2 (by decide +kernel) x hx hd ho).elim

theorem bound4578 : BoxMajorant Geometry.b4578 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4578.Widths)
  · have he : Geometry.b4578.half 2 false=Geometry.b4909 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4909
  · have he : Geometry.b4578.half 2 true=Geometry.b4910 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4910

theorem bound4577 : BoxMajorant Geometry.b4577 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4577 2 (by decide +kernel) x hx hd ho).elim

theorem bound4310 : BoxMajorant Geometry.b4310 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4310.Widths)
  · have he : Geometry.b4310.half 1 false=Geometry.b4577 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4577
  · have he : Geometry.b4310.half 1 true=Geometry.b4578 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4578

theorem bound4309 : BoxMajorant Geometry.b4309 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4309 2 (by decide +kernel) x hx hd ho).elim

theorem bound3956 : BoxMajorant Geometry.b3956 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3956.Widths)
  · have he : Geometry.b3956.half 0 false=Geometry.b4309 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4309
  · have he : Geometry.b3956.half 0 true=Geometry.b4310 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4310

theorem bound3955 : BoxMajorant Geometry.b3955 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3955 2 (by decide +kernel) x hx hd ho).elim

theorem bound3600 : BoxMajorant Geometry.b3600 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3600.Widths)
  · have he : Geometry.b3600.half 2 false=Geometry.b3955 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3955
  · have he : Geometry.b3600.half 2 true=Geometry.b3956 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3956

theorem bound3599 : BoxMajorant Geometry.b3599 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3599 2 (by decide +kernel) x hx hd ho).elim

theorem bound3330 : BoxMajorant Geometry.b3330 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3330.Widths)
  · have he : Geometry.b3330.half 1 false=Geometry.b3599 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3599
  · have he : Geometry.b3330.half 1 true=Geometry.b3600 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3600

theorem bound3329 : BoxMajorant Geometry.b3329 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3329 2 (by decide +kernel) x hx hd ho).elim

theorem bound2994 : BoxMajorant Geometry.b2994 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2994.Widths)
  · have he : Geometry.b2994.half 0 false=Geometry.b3329 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3329
  · have he : Geometry.b2994.half 0 true=Geometry.b3330 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3330

end N7.Kernel.Cover
