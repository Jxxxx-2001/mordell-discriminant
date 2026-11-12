import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.PositiveGroups.G0309
import N7.Kernel.PositiveGroups.G0361
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4104 : BoxMajorant Geometry.b4104 := by
  exact PositiveLeaves.L469.bound

theorem bound4103 : BoxMajorant Geometry.b4103 := by
  exact PositiveLeaves.L470.bound

theorem bound3702 : BoxMajorant Geometry.b3702 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3702.Widths)
  · have he : Geometry.b3702.half 2 false=Geometry.b4103 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4103
  · have he : Geometry.b3702.half 2 true=Geometry.b4104 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4104

theorem bound3701 : BoxMajorant Geometry.b3701 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3701 0 (by decide +kernel) x hx hd ho).elim

theorem bound3436 : BoxMajorant Geometry.b3436 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3436 0 (by decide +kernel) x hx hd ho).elim

theorem bound3435 : BoxMajorant Geometry.b3435 := by
  exact PositiveLeaves.L467.bound

theorem bound3434 : BoxMajorant Geometry.b3434 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3434 0 (by decide +kernel) x hx hd ho).elim

theorem bound3433 : BoxMajorant Geometry.b3433 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3433.Widths)
  · have he : Geometry.b3433.half 1 false=Geometry.b3701 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3701
  · have he : Geometry.b3433.half 1 true=Geometry.b3702 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3702

theorem bound3154 : BoxMajorant Geometry.b3154 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3154.Widths)
  · have he : Geometry.b3154.half 0 false=Geometry.b3435 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3435
  · have he : Geometry.b3154.half 0 true=Geometry.b3436 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3436

theorem bound3153 : BoxMajorant Geometry.b3153 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3153.Widths)
  · have he : Geometry.b3153.half 0 false=Geometry.b3433 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3433
  · have he : Geometry.b3153.half 0 true=Geometry.b3434 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3434

theorem bound2759 : BoxMajorant Geometry.b2759 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2759.Widths)
  · have he : Geometry.b2759.half 2 false=Geometry.b3153 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3153
  · have he : Geometry.b2759.half 2 true=Geometry.b3154 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3154

end N7.Kernel.Cover
