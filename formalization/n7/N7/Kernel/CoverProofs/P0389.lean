import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.PositiveGroups.G0450
import N7.Kernel.PositiveGroups.G0451
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5060 : BoxMajorant Geometry.b5060 := by
  exact PositiveLeaves.L442.bound

theorem bound5059 : BoxMajorant Geometry.b5059 := by
  exact PositiveLeaves.L443.bound

theorem bound4684 : BoxMajorant Geometry.b4684 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4684.Widths)
  · have he : Geometry.b4684.half 2 false=Geometry.b5059 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5059
  · have he : Geometry.b4684.half 2 true=Geometry.b5060 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5060

theorem bound4683 : BoxMajorant Geometry.b4683 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4683 0 (by decide +kernel) x hx hd ho).elim

theorem bound4415 : BoxMajorant Geometry.b4415 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4415.Widths)
  · have he : Geometry.b4415.half 1 false=Geometry.b4683 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4683
  · have he : Geometry.b4415.half 1 true=Geometry.b4684 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4684

end N7.Kernel.Cover
