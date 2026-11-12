import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.PositiveGroups.G0089
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1738 : BoxMajorant Geometry.b1738 := by
  exact PositiveLeaves.L1093.bound

theorem bound1737 : BoxMajorant Geometry.b1737 := by
  exact PositiveLeaves.L1094.bound

theorem bound1220 : BoxMajorant Geometry.b1220 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1220.Widths)
  · have he : Geometry.b1220.half 2 false=Geometry.b1737 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1737
  · have he : Geometry.b1220.half 2 true=Geometry.b1738 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1738

theorem bound1219 : BoxMajorant Geometry.b1219 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1219 0 (by decide +kernel) x hx hd ho).elim

theorem bound883 : BoxMajorant Geometry.b883 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b883.Widths)
  · have he : Geometry.b883.half 1 false=Geometry.b1219 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1219
  · have he : Geometry.b883.half 1 true=Geometry.b1220 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1220

end N7.Kernel.Cover
