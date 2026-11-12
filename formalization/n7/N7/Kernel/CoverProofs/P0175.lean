import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0172
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2066 : BoxMajorant Geometry.b2066 := by
  exact PositiveLeaves.L59.bound

theorem bound2065 : BoxMajorant Geometry.b2065 := by
  exact PositiveLeaves.L60.bound

theorem bound1422 : BoxMajorant Geometry.b1422 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1422.Widths)
  · have he : Geometry.b1422.half 2 false=Geometry.b2065 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2065
  · have he : Geometry.b1422.half 2 true=Geometry.b2066 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2066

theorem bound1421 : BoxMajorant Geometry.b1421 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1421 0 (by decide +kernel) x hx hd ho).elim

theorem bound1013 : BoxMajorant Geometry.b1013 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1013.Widths)
  · have he : Geometry.b1013.half 1 false=Geometry.b1421 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1421
  · have he : Geometry.b1013.half 1 true=Geometry.b1422 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1422

end N7.Kernel.Cover
