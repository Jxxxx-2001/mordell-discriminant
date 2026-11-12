import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.PositiveGroups.G0009
import N7.Kernel.PositiveGroups.G0040
import N7.Kernel.PositiveGroups.G0065
import N7.Kernel.PositiveGroups.G0066
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2562 : BoxMajorant Geometry.b2562 := by
  exact PositiveLeaves.L2272.bound

theorem bound2561 : BoxMajorant Geometry.b2561 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2561 2 (by decide +kernel) x hx hd ho).elim

theorem bound2200 : BoxMajorant Geometry.b2200 := by
  exact PositiveLeaves.L2271.bound

theorem bound2199 : BoxMajorant Geometry.b2199 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2199.Widths)
  · have he : Geometry.b2199.half 1 false=Geometry.b2561 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2561
  · have he : Geometry.b2199.half 1 true=Geometry.b2562 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2562

theorem bound1580 : BoxMajorant Geometry.b1580 := by
  exact PositiveLeaves.L2270.bound

theorem bound1579 : BoxMajorant Geometry.b1579 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1579.Widths)
  · have he : Geometry.b1579.half 0 false=Geometry.b2199 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2199
  · have he : Geometry.b1579.half 0 true=Geometry.b2200 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2200

theorem bound1122 : BoxMajorant Geometry.b1122 := by
  exact PositiveLeaves.L2269.bound

theorem bound1121 : BoxMajorant Geometry.b1121 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1121.Widths)
  · have he : Geometry.b1121.half 2 false=Geometry.b1579 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1579
  · have he : Geometry.b1121.half 2 true=Geometry.b1580 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1580

theorem bound812 : BoxMajorant Geometry.b812 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b812.Widths)
  · have he : Geometry.b812.half 1 false=Geometry.b1121 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1121
  · have he : Geometry.b812.half 1 true=Geometry.b1122 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1122

end N7.Kernel.Cover
