import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.PositiveGroups.G0057
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1756 : BoxMajorant Geometry.b1756 := by
  exact PositiveLeaves.L1067.bound

theorem bound1755 : BoxMajorant Geometry.b1755 := by
  exact PositiveLeaves.L1068.bound

theorem bound1230 : BoxMajorant Geometry.b1230 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1230.Widths)
  · have he : Geometry.b1230.half 2 false=Geometry.b1755 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1755
  · have he : Geometry.b1230.half 2 true=Geometry.b1756 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1756

theorem bound1229 : BoxMajorant Geometry.b1229 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1229 0 (by decide +kernel) x hx hd ho).elim

theorem bound891 : BoxMajorant Geometry.b891 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b891.Widths)
  · have he : Geometry.b891.half 1 false=Geometry.b1229 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1229
  · have he : Geometry.b891.half 1 true=Geometry.b1230 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1230

end N7.Kernel.Cover
