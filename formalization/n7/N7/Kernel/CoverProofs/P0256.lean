import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.PositiveGroups.G0338
import N7.Kernel.PositiveGroups.G0367
import N7.Kernel.PositiveGroups.G0398
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4970 : BoxMajorant Geometry.b4970 := by
  exact PositiveLeaves.L1624.bound

theorem bound4969 : BoxMajorant Geometry.b4969 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4969 2 (by decide +kernel) x hx hd ho).elim

theorem bound4620 : BoxMajorant Geometry.b4620 := by
  exact PositiveLeaves.L1623.bound

theorem bound4619 : BoxMajorant Geometry.b4619 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4619.Widths)
  · have he : Geometry.b4619.half 2 false=Geometry.b4969 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4969
  · have he : Geometry.b4619.half 2 true=Geometry.b4970 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4970

theorem bound4354 : BoxMajorant Geometry.b4354 := by
  exact PositiveLeaves.L1620.bound

theorem bound4353 : BoxMajorant Geometry.b4353 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4353 2 (by decide +kernel) x hx hd ho).elim

theorem bound4352 : BoxMajorant Geometry.b4352 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4352.Widths)
  · have he : Geometry.b4352.half 1 false=Geometry.b4619 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4619
  · have he : Geometry.b4352.half 1 true=Geometry.b4620 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4620

theorem bound4351 : BoxMajorant Geometry.b4351 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4351 2 (by decide +kernel) x hx hd ho).elim

theorem bound3998 : BoxMajorant Geometry.b3998 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3998.Widths)
  · have he : Geometry.b3998.half 0 false=Geometry.b4353 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4353
  · have he : Geometry.b3998.half 0 true=Geometry.b4354 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4354

theorem bound3997 : BoxMajorant Geometry.b3997 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3997 2 (by decide +kernel) x hx hd ho).elim

theorem bound3996 : BoxMajorant Geometry.b3996 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3996.Widths)
  · have he : Geometry.b3996.half 0 false=Geometry.b4351 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4351
  · have he : Geometry.b3996.half 0 true=Geometry.b4352 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4352

theorem bound3995 : BoxMajorant Geometry.b3995 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3995 2 (by decide +kernel) x hx hd ho).elim

theorem bound3626 : BoxMajorant Geometry.b3626 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3626.Widths)
  · have he : Geometry.b3626.half 2 false=Geometry.b3997 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3997
  · have he : Geometry.b3626.half 2 true=Geometry.b3998 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3998

theorem bound3625 : BoxMajorant Geometry.b3625 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3625.Widths)
  · have he : Geometry.b3625.half 2 false=Geometry.b3995 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3995
  · have he : Geometry.b3625.half 2 true=Geometry.b3996 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3996

theorem bound3352 : BoxMajorant Geometry.b3352 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3352.Widths)
  · have he : Geometry.b3352.half 1 false=Geometry.b3625 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3625
  · have he : Geometry.b3352.half 1 true=Geometry.b3626 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3626

theorem bound3351 : BoxMajorant Geometry.b3351 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3351 2 (by decide +kernel) x hx hd ho).elim

theorem bound3010 : BoxMajorant Geometry.b3010 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3010.Widths)
  · have he : Geometry.b3010.half 0 false=Geometry.b3351 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3351
  · have he : Geometry.b3010.half 0 true=Geometry.b3352 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3352

theorem bound3009 : BoxMajorant Geometry.b3009 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3009 2 (by decide +kernel) x hx hd ho).elim

theorem bound2619 : BoxMajorant Geometry.b2619 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2619.Widths)
  · have he : Geometry.b2619.half 2 false=Geometry.b3009 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3009
  · have he : Geometry.b2619.half 2 true=Geometry.b3010 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3010

end N7.Kernel.Cover
