import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.PositiveGroups.G0072
import N7.Kernel.PositiveGroups.G0107
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2500 : BoxMajorant Geometry.b2500 := by
  exact PositiveLeaves.L2531.bound

theorem bound2499 : BoxMajorant Geometry.b2499 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2499 2 (by decide +kernel) x hx hd ho).elim

theorem bound2142 : BoxMajorant Geometry.b2142 := by
  exact PositiveLeaves.L2530.bound

theorem bound2141 : BoxMajorant Geometry.b2141 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2141.Widths)
  · have he : Geometry.b2141.half 1 false=Geometry.b2499 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2499
  · have he : Geometry.b2141.half 1 true=Geometry.b2500 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2500

theorem bound2140 : BoxMajorant Geometry.b2140 := by
  exact PositiveLeaves.L2534.bound

theorem bound2139 : BoxMajorant Geometry.b2139 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2139 2 (by decide +kernel) x hx hd ho).elim

theorem bound1496 : BoxMajorant Geometry.b1496 := by
  exact PositiveLeaves.L2528.bound

theorem bound1495 : BoxMajorant Geometry.b1495 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1495 2 (by decide +kernel) x hx hd ho).elim

theorem bound1494 : BoxMajorant Geometry.b1494 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1494.Widths)
  · have he : Geometry.b1494.half 0 false=Geometry.b2141 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2141
  · have he : Geometry.b1494.half 0 true=Geometry.b2142 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2142

theorem bound1493 : BoxMajorant Geometry.b1493 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1493 2 (by decide +kernel) x hx hd ho).elim

theorem bound1492 : BoxMajorant Geometry.b1492 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1492.Widths)
  · have he : Geometry.b1492.half 0 false=Geometry.b2139 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2139
  · have he : Geometry.b1492.half 0 true=Geometry.b2140 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2140

theorem bound1491 : BoxMajorant Geometry.b1491 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1491 2 (by decide +kernel) x hx hd ho).elim

theorem bound1064 : BoxMajorant Geometry.b1064 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1064.Widths)
  · have he : Geometry.b1064.half 2 false=Geometry.b1495 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1495
  · have he : Geometry.b1064.half 2 true=Geometry.b1496 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1496

theorem bound1063 : BoxMajorant Geometry.b1063 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1063.Widths)
  · have he : Geometry.b1063.half 2 false=Geometry.b1493 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1493
  · have he : Geometry.b1063.half 2 true=Geometry.b1494 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1494

theorem bound1062 : BoxMajorant Geometry.b1062 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1062.Widths)
  · have he : Geometry.b1062.half 2 false=Geometry.b1491 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1491
  · have he : Geometry.b1062.half 2 true=Geometry.b1492 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1492

theorem bound1061 : BoxMajorant Geometry.b1061 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1061 2 (by decide +kernel) x hx hd ho).elim

theorem bound770 : BoxMajorant Geometry.b770 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b770.Widths)
  · have he : Geometry.b770.half 1 false=Geometry.b1063 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1063
  · have he : Geometry.b770.half 1 true=Geometry.b1064 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1064

theorem bound769 : BoxMajorant Geometry.b769 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b769.Widths)
  · have he : Geometry.b769.half 1 false=Geometry.b1061 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1061
  · have he : Geometry.b769.half 1 true=Geometry.b1062 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1062

theorem bound494 : BoxMajorant Geometry.b494 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b494.Widths)
  · have he : Geometry.b494.half 0 false=Geometry.b769 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound769
  · have he : Geometry.b494.half 0 true=Geometry.b770 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound770

end N7.Kernel.Cover
