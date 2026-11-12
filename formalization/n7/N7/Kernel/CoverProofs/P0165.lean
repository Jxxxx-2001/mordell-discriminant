import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.PositiveGroups.G0138
import N7.Kernel.PositiveGroups.G0175
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2444 : BoxMajorant Geometry.b2444 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2444 0 (by decide +kernel) x hx hd ho).elim

theorem bound2443 : BoxMajorant Geometry.b2443 := by
  exact PositiveLeaves.L116.bound

theorem bound2054 : BoxMajorant Geometry.b2054 := by
  exact PositiveLeaves.L114.bound

theorem bound2053 : BoxMajorant Geometry.b2053 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2053.Widths)
  · have he : Geometry.b2053.half 0 false=Geometry.b2443 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2443
  · have he : Geometry.b2053.half 0 true=Geometry.b2444 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2444

theorem bound1410 : BoxMajorant Geometry.b1410 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1410.Widths)
  · have he : Geometry.b1410.half 2 false=Geometry.b2053 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2053
  · have he : Geometry.b1410.half 2 true=Geometry.b2054 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2054

theorem bound1409 : BoxMajorant Geometry.b1409 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1409 0 (by decide +kernel) x hx hd ho).elim

theorem bound1002 : BoxMajorant Geometry.b1002 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1002 0 (by decide +kernel) x hx hd ho).elim

theorem bound1001 : BoxMajorant Geometry.b1001 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1001.Widths)
  · have he : Geometry.b1001.half 1 false=Geometry.b1409 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1409
  · have he : Geometry.b1001.half 1 true=Geometry.b1410 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1410

theorem bound699 : BoxMajorant Geometry.b699 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b699.Widths)
  · have he : Geometry.b699.half 0 false=Geometry.b1001 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1001
  · have he : Geometry.b699.half 0 true=Geometry.b1002 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1002

end N7.Kernel.Cover
