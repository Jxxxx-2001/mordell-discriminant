import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.PositiveGroups.G0225
import N7.Kernel.PositiveGroups.G0261
import N7.Kernel.PositiveGroups.G0311
import N7.Kernel.PositiveGroups.G0335
import N7.Kernel.PositiveGroups.G0336
import N7.Kernel.PositiveGroups.G0365
import N7.Kernel.PositiveGroups.G0366
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4978 : BoxMajorant Geometry.b4978 := by
  exact PositiveLeaves.L1580.bound

theorem bound4977 : BoxMajorant Geometry.b4977 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4977 2 (by decide +kernel) x hx hd ho).elim

theorem bound4976 : BoxMajorant Geometry.b4976 := by
  exact PositiveLeaves.L1584.bound

theorem bound4975 : BoxMajorant Geometry.b4975 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4975 2 (by decide +kernel) x hx hd ho).elim

theorem bound4974 : BoxMajorant Geometry.b4974 := by
  exact PositiveLeaves.L1586.bound

theorem bound4973 : BoxMajorant Geometry.b4973 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4973 2 (by decide +kernel) x hx hd ho).elim

theorem bound4628 : BoxMajorant Geometry.b4628 := by
  exact PositiveLeaves.L1579.bound

theorem bound4627 : BoxMajorant Geometry.b4627 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4627.Widths)
  · have he : Geometry.b4627.half 2 false=Geometry.b4977 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4977
  · have he : Geometry.b4627.half 2 true=Geometry.b4978 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4978

theorem bound4626 : BoxMajorant Geometry.b4626 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4626.Widths)
  · have he : Geometry.b4626.half 2 false=Geometry.b4975 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4975
  · have he : Geometry.b4626.half 2 true=Geometry.b4976 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4976

theorem bound4625 : BoxMajorant Geometry.b4625 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4625.Widths)
  · have he : Geometry.b4625.half 2 false=Geometry.b4973 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4973
  · have he : Geometry.b4625.half 2 true=Geometry.b4974 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4974

theorem bound4368 : BoxMajorant Geometry.b4368 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4368.Widths)
  · have he : Geometry.b4368.half 1 false=Geometry.b4627 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4627
  · have he : Geometry.b4368.half 1 true=Geometry.b4628 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4628

theorem bound4367 : BoxMajorant Geometry.b4367 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4367 2 (by decide +kernel) x hx hd ho).elim

theorem bound4366 : BoxMajorant Geometry.b4366 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4366.Widths)
  · have he : Geometry.b4366.half 1 false=Geometry.b4625 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4625
  · have he : Geometry.b4366.half 1 true=Geometry.b4626 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4626

theorem bound4365 : BoxMajorant Geometry.b4365 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4365 2 (by decide +kernel) x hx hd ho).elim

theorem bound4018 : BoxMajorant Geometry.b4018 := by
  exact PositiveLeaves.L1578.bound

theorem bound4017 : BoxMajorant Geometry.b4017 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4017.Widths)
  · have he : Geometry.b4017.half 0 false=Geometry.b4367 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4367
  · have he : Geometry.b4017.half 0 true=Geometry.b4368 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4368

theorem bound4016 : BoxMajorant Geometry.b4016 := by
  exact PositiveLeaves.L1583.bound

theorem bound4015 : BoxMajorant Geometry.b4015 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4015.Widths)
  · have he : Geometry.b4015.half 0 false=Geometry.b4365 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4365
  · have he : Geometry.b4015.half 0 true=Geometry.b4366 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4366

theorem bound3638 : BoxMajorant Geometry.b3638 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3638.Widths)
  · have he : Geometry.b3638.half 2 false=Geometry.b4017 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4017
  · have he : Geometry.b3638.half 2 true=Geometry.b4018 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4018

theorem bound3637 : BoxMajorant Geometry.b3637 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3637.Widths)
  · have he : Geometry.b3637.half 2 false=Geometry.b4015 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4015
  · have he : Geometry.b3637.half 2 true=Geometry.b4016 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4016

theorem bound3362 : BoxMajorant Geometry.b3362 := by
  exact PositiveLeaves.L1577.bound

theorem bound3361 : BoxMajorant Geometry.b3361 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3361.Widths)
  · have he : Geometry.b3361.half 1 false=Geometry.b3637 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3637
  · have he : Geometry.b3361.half 1 true=Geometry.b3638 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3638

theorem bound3018 : BoxMajorant Geometry.b3018 := by
  exact PositiveLeaves.L1576.bound

theorem bound3017 : BoxMajorant Geometry.b3017 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3017.Widths)
  · have he : Geometry.b3017.half 0 false=Geometry.b3361 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3361
  · have he : Geometry.b3017.half 0 true=Geometry.b3362 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3362

theorem bound2623 : BoxMajorant Geometry.b2623 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2623.Widths)
  · have he : Geometry.b2623.half 2 false=Geometry.b3017 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3017
  · have he : Geometry.b2623.half 2 true=Geometry.b3018 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3018

end N7.Kernel.Cover
