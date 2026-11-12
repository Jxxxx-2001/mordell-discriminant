import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.PositiveGroups.G0292
import N7.Kernel.PositiveGroups.G0315
import N7.Kernel.PositiveGroups.G0316
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4242 : BoxMajorant Geometry.b4242 := by
  exact PositiveLeaves.L2026.bound

theorem bound4241 : BoxMajorant Geometry.b4241 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4241 2 (by decide +kernel) x hx hd ho).elim

theorem bound3872 : BoxMajorant Geometry.b3872 := by
  exact PositiveLeaves.L2025.bound

theorem bound3871 : BoxMajorant Geometry.b3871 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3871.Widths)
  · have he : Geometry.b3871.half 0 false=Geometry.b4241 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4241
  · have he : Geometry.b3871.half 0 true=Geometry.b4242 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4242

theorem bound3870 : BoxMajorant Geometry.b3870 := by
  exact PositiveLeaves.L2028.bound

theorem bound3869 : BoxMajorant Geometry.b3869 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3869 2 (by decide +kernel) x hx hd ho).elim

theorem bound3550 : BoxMajorant Geometry.b3550 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3550.Widths)
  · have he : Geometry.b3550.half 2 false=Geometry.b3871 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3871
  · have he : Geometry.b3550.half 2 true=Geometry.b3872 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3872

theorem bound3549 : BoxMajorant Geometry.b3549 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3549.Widths)
  · have he : Geometry.b3549.half 2 false=Geometry.b3869 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3869
  · have he : Geometry.b3549.half 2 true=Geometry.b3870 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3870

theorem bound3274 : BoxMajorant Geometry.b3274 := by
  exact PositiveLeaves.L2024.bound

theorem bound3273 : BoxMajorant Geometry.b3273 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3273.Widths)
  · have he : Geometry.b3273.half 1 false=Geometry.b3549 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3549
  · have he : Geometry.b3273.half 1 true=Geometry.b3550 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3550

theorem bound2944 : BoxMajorant Geometry.b2944 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2944.Widths)
  · have he : Geometry.b2944.half 0 false=Geometry.b3273 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3273
  · have he : Geometry.b2944.half 0 true=Geometry.b3274 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3274

end N7.Kernel.Cover
