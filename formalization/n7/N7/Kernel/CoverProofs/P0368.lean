import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.PositiveGroups.G0422
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5168 : BoxMajorant Geometry.b5168 := by
  exact PositiveLeaves.L2051.bound

theorem bound5167 : BoxMajorant Geometry.b5167 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5167 2 (by decide +kernel) x hx hd ho).elim

theorem bound4838 : BoxMajorant Geometry.b4838 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4838.Widths)
  · have he : Geometry.b4838.half 0 false=Geometry.b5167 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5167
  · have he : Geometry.b4838.half 0 true=Geometry.b5168 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5168

end N7.Kernel.Cover
