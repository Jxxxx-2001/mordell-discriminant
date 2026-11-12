import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0256
import N7.Kernel.PositiveGroups.G0308
import N7.Kernel.PositiveGroups.G0332
import N7.Kernel.PositiveGroups.G0359
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5402 : BoxMajorant Geometry.b5402 := by
  exact PositiveLeaves.L172.bound

theorem bound5401 : BoxMajorant Geometry.b5401 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5401 0 (by decide +kernel) x hx hd ho).elim

theorem bound5280 : BoxMajorant Geometry.b5280 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5280 0 (by decide +kernel) x hx hd ho).elim

theorem bound5279 : BoxMajorant Geometry.b5279 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5279.Widths)
  · have he : Geometry.b5279.half 1 false=Geometry.b5401 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5401
  · have he : Geometry.b5279.half 1 true=Geometry.b5402 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5402

theorem bound5102 : BoxMajorant Geometry.b5102 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5102.Widths)
  · have he : Geometry.b5102.half 0 false=Geometry.b5279 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5279
  · have he : Geometry.b5102.half 0 true=Geometry.b5280 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5280

theorem bound5101 : BoxMajorant Geometry.b5101 := by
  exact PositiveLeaves.L174.bound

theorem bound4716 : BoxMajorant Geometry.b4716 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4716.Widths)
  · have he : Geometry.b4716.half 2 false=Geometry.b5101 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5101
  · have he : Geometry.b4716.half 2 true=Geometry.b5102 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5102

theorem bound4715 : BoxMajorant Geometry.b4715 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4715 0 (by decide +kernel) x hx hd ho).elim

theorem bound4438 : BoxMajorant Geometry.b4438 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4438 0 (by decide +kernel) x hx hd ho).elim

theorem bound4437 : BoxMajorant Geometry.b4437 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4437.Widths)
  · have he : Geometry.b4437.half 1 false=Geometry.b4715 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4715
  · have he : Geometry.b4437.half 1 true=Geometry.b4716 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4716

theorem bound4146 : BoxMajorant Geometry.b4146 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4146.Widths)
  · have he : Geometry.b4146.half 0 false=Geometry.b4437 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4437
  · have he : Geometry.b4146.half 0 true=Geometry.b4438 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4438

theorem bound4145 : BoxMajorant Geometry.b4145 := by
  exact PositiveLeaves.L176.bound

theorem bound3726 : BoxMajorant Geometry.b3726 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3726.Widths)
  · have he : Geometry.b3726.half 2 false=Geometry.b4145 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4145
  · have he : Geometry.b3726.half 2 true=Geometry.b4146 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4146

theorem bound3725 : BoxMajorant Geometry.b3725 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3725 0 (by decide +kernel) x hx hd ho).elim

theorem bound3450 : BoxMajorant Geometry.b3450 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3450 0 (by decide +kernel) x hx hd ho).elim

theorem bound3449 : BoxMajorant Geometry.b3449 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3449.Widths)
  · have he : Geometry.b3449.half 1 false=Geometry.b3725 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3725
  · have he : Geometry.b3449.half 1 true=Geometry.b3726 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3726

theorem bound3168 : BoxMajorant Geometry.b3168 := by
  exact PositiveLeaves.L168.bound

theorem bound3167 : BoxMajorant Geometry.b3167 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3167.Widths)
  · have he : Geometry.b3167.half 0 false=Geometry.b3449 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3449
  · have he : Geometry.b3167.half 0 true=Geometry.b3450 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3450

theorem bound2770 : BoxMajorant Geometry.b2770 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2770.Widths)
  · have he : Geometry.b2770.half 2 false=Geometry.b3167 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3167
  · have he : Geometry.b2770.half 2 true=Geometry.b3168 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3168

end N7.Kernel.Cover
