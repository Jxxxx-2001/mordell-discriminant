import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.PositiveGroups.G0438
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5328 : BoxMajorant Geometry.b5328 := by
  exact PositiveLeaves.L2625.bound

theorem bound5327 : BoxMajorant Geometry.b5327 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5327 2 (by decide +kernel) x hx hd ho).elim

theorem bound5146 : BoxMajorant Geometry.b5146 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5146.Widths)
  · have he : Geometry.b5146.half 1 false=Geometry.b5327 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5327
  · have he : Geometry.b5146.half 1 true=Geometry.b5328 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5328

theorem bound5145 : BoxMajorant Geometry.b5145 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5145 2 (by decide +kernel) x hx hd ho).elim

theorem bound4790 : BoxMajorant Geometry.b4790 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4790.Widths)
  · have he : Geometry.b4790.half 0 false=Geometry.b5145 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5145
  · have he : Geometry.b4790.half 0 true=Geometry.b5146 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5146

end N7.Kernel.Cover
