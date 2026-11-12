import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.PositiveGroups.G0287
import N7.Kernel.PositiveGroups.G0336
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4374 : BoxMajorant Geometry.b4374 := by
  exact PositiveLeaves.L1558.bound

theorem bound4373 : BoxMajorant Geometry.b4373 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4373 2 (by decide +kernel) x hx hd ho).elim

theorem bound4026 : BoxMajorant Geometry.b4026 := by
  exact PositiveLeaves.L1556.bound

theorem bound4025 : BoxMajorant Geometry.b4025 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4025 2 (by decide +kernel) x hx hd ho).elim

theorem bound4024 : BoxMajorant Geometry.b4024 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4024.Widths)
  · have he : Geometry.b4024.half 0 false=Geometry.b4373 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4373
  · have he : Geometry.b4024.half 0 true=Geometry.b4374 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4374

theorem bound4023 : BoxMajorant Geometry.b4023 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4023 2 (by decide +kernel) x hx hd ho).elim

theorem bound3642 : BoxMajorant Geometry.b3642 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3642.Widths)
  · have he : Geometry.b3642.half 2 false=Geometry.b4025 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4025
  · have he : Geometry.b3642.half 2 true=Geometry.b4026 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4026

theorem bound3641 : BoxMajorant Geometry.b3641 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3641.Widths)
  · have he : Geometry.b3641.half 2 false=Geometry.b4023 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4023
  · have he : Geometry.b3641.half 2 true=Geometry.b4024 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4024

theorem bound3366 : BoxMajorant Geometry.b3366 := by
  exact PositiveLeaves.L1555.bound

theorem bound3365 : BoxMajorant Geometry.b3365 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3365.Widths)
  · have he : Geometry.b3365.half 1 false=Geometry.b3641 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3641
  · have he : Geometry.b3365.half 1 true=Geometry.b3642 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3642

theorem bound3022 : BoxMajorant Geometry.b3022 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3022.Widths)
  · have he : Geometry.b3022.half 0 false=Geometry.b3365 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3365
  · have he : Geometry.b3022.half 0 true=Geometry.b3366 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3366

theorem bound3021 : BoxMajorant Geometry.b3021 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3021 2 (by decide +kernel) x hx hd ho).elim

theorem bound2625 : BoxMajorant Geometry.b2625 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2625.Widths)
  · have he : Geometry.b2625.half 2 false=Geometry.b3021 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3021
  · have he : Geometry.b2625.half 2 true=Geometry.b3022 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3022

end N7.Kernel.Cover
