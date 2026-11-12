import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0418
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5194 : BoxMajorant Geometry.b5194 := by
  exact PositiveLeaves.L1733.bound

theorem bound5193 : BoxMajorant Geometry.b5193 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5193 2 (by decide +kernel) x hx hd ho).elim

theorem bound4928 : BoxMajorant Geometry.b4928 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4928.Widths)
  · have he : Geometry.b4928.half 0 false=Geometry.b5193 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5193
  · have he : Geometry.b4928.half 0 true=Geometry.b5194 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5194

end N7.Kernel.Cover
