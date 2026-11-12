import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.PositiveGroups.G0089
import N7.Kernel.PositiveGroups.G0130
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2306 : BoxMajorant Geometry.b2306 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2306 0 (by decide +kernel) x hx hd ho).elim

theorem bound2305 : BoxMajorant Geometry.b2305 := by
  exact PositiveLeaves.L1099.bound

theorem bound1736 : BoxMajorant Geometry.b1736 := by
  exact PositiveLeaves.L1097.bound

theorem bound1735 : BoxMajorant Geometry.b1735 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1735.Widths)
  · have he : Geometry.b1735.half 0 false=Geometry.b2305 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2305
  · have he : Geometry.b1735.half 0 true=Geometry.b2306 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2306

theorem bound1218 : BoxMajorant Geometry.b1218 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1218.Widths)
  · have he : Geometry.b1218.half 2 false=Geometry.b1735 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1735
  · have he : Geometry.b1218.half 2 true=Geometry.b1736 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1736

theorem bound1217 : BoxMajorant Geometry.b1217 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1217 0 (by decide +kernel) x hx hd ho).elim

theorem bound881 : BoxMajorant Geometry.b881 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b881.Widths)
  · have he : Geometry.b881.half 1 false=Geometry.b1217 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1217
  · have he : Geometry.b881.half 1 true=Geometry.b1218 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1218

end N7.Kernel.Cover
