import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.PositiveGroups.G0000
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound166 : BoxMajorant Geometry.b166 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b166 1 (by decide +kernel) x hx hd ho).elim

theorem bound165 : BoxMajorant Geometry.b165 := by
  exact PositiveLeaves.L577.bound

theorem bound96 : BoxMajorant Geometry.b96 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b96.Widths)
  · have he : Geometry.b96.half 2 false=Geometry.b165 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound165
  · have he : Geometry.b96.half 2 true=Geometry.b166 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound166

theorem bound95 : BoxMajorant Geometry.b95 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b95 1 (by decide +kernel) x hx hd ho).elim

theorem bound51 : BoxMajorant Geometry.b51 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b51.Widths)
  · have he : Geometry.b51.half 1 false=Geometry.b95 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound95
  · have he : Geometry.b51.half 1 true=Geometry.b96 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound96

end N7.Kernel.Cover
