import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.PositiveGroups.G0064
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2012 : BoxMajorant Geometry.b2012 := by
  exact PositiveLeaves.L502.bound

theorem bound2011 : BoxMajorant Geometry.b2011 := by
  exact PositiveLeaves.L503.bound

theorem bound1388 : BoxMajorant Geometry.b1388 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1388.Widths)
  · have he : Geometry.b1388.half 2 false=Geometry.b2011 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2011
  · have he : Geometry.b1388.half 2 true=Geometry.b2012 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2012

theorem bound1387 : BoxMajorant Geometry.b1387 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1387 0 (by decide +kernel) x hx hd ho).elim

theorem bound988 : BoxMajorant Geometry.b988 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b988 0 (by decide +kernel) x hx hd ho).elim

theorem bound987 : BoxMajorant Geometry.b987 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b987.Widths)
  · have he : Geometry.b987.half 1 false=Geometry.b1387 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1387
  · have he : Geometry.b987.half 1 true=Geometry.b1388 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1388

theorem bound692 : BoxMajorant Geometry.b692 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b692.Widths)
  · have he : Geometry.b692.half 0 false=Geometry.b987 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound987
  · have he : Geometry.b692.half 0 true=Geometry.b988 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound988

end N7.Kernel.Cover
