import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.PositiveGroups.G0143
import N7.Kernel.PositiveGroups.G0179
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2884 : BoxMajorant Geometry.b2884 := by
  exact PositiveLeaves.L2348.bound

theorem bound2883 : BoxMajorant Geometry.b2883 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2883 2 (by decide +kernel) x hx hd ho).elim

theorem bound2882 : BoxMajorant Geometry.b2882 := by
  exact PositiveLeaves.L2350.bound

theorem bound2881 : BoxMajorant Geometry.b2881 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2881 2 (by decide +kernel) x hx hd ho).elim

theorem bound2880 : BoxMajorant Geometry.b2880 := by
  exact PositiveLeaves.L2354.bound

theorem bound2879 : BoxMajorant Geometry.b2879 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2879 2 (by decide +kernel) x hx hd ho).elim

theorem bound2538 : BoxMajorant Geometry.b2538 := by
  exact PositiveLeaves.L2347.bound

theorem bound2537 : BoxMajorant Geometry.b2537 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2537.Widths)
  · have he : Geometry.b2537.half 2 false=Geometry.b2883 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2883
  · have he : Geometry.b2537.half 2 true=Geometry.b2884 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2884

theorem bound2536 : BoxMajorant Geometry.b2536 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2536.Widths)
  · have he : Geometry.b2536.half 2 false=Geometry.b2881 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2881
  · have he : Geometry.b2536.half 2 true=Geometry.b2882 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2882

theorem bound2535 : BoxMajorant Geometry.b2535 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2535 2 (by decide +kernel) x hx hd ho).elim

theorem bound2534 : BoxMajorant Geometry.b2534 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2534.Widths)
  · have he : Geometry.b2534.half 2 false=Geometry.b2879 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2879
  · have he : Geometry.b2534.half 2 true=Geometry.b2880 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2880

theorem bound2533 : BoxMajorant Geometry.b2533 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2533 2 (by decide +kernel) x hx hd ho).elim

theorem bound2178 : BoxMajorant Geometry.b2178 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2178.Widths)
  · have he : Geometry.b2178.half 1 false=Geometry.b2537 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2537
  · have he : Geometry.b2178.half 1 true=Geometry.b2538 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2538

theorem bound2177 : BoxMajorant Geometry.b2177 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2177.Widths)
  · have he : Geometry.b2177.half 1 false=Geometry.b2535 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2535
  · have he : Geometry.b2177.half 1 true=Geometry.b2536 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2536

theorem bound2176 : BoxMajorant Geometry.b2176 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2176.Widths)
  · have he : Geometry.b2176.half 1 false=Geometry.b2533 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2533
  · have he : Geometry.b2176.half 1 true=Geometry.b2534 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2534

theorem bound2175 : BoxMajorant Geometry.b2175 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2175 2 (by decide +kernel) x hx hd ho).elim

theorem bound1554 : BoxMajorant Geometry.b1554 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1554.Widths)
  · have he : Geometry.b1554.half 0 false=Geometry.b2177 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2177
  · have he : Geometry.b1554.half 0 true=Geometry.b2178 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2178

theorem bound1553 : BoxMajorant Geometry.b1553 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1553 2 (by decide +kernel) x hx hd ho).elim

theorem bound1552 : BoxMajorant Geometry.b1552 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1552.Widths)
  · have he : Geometry.b1552.half 0 false=Geometry.b2175 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2175
  · have he : Geometry.b1552.half 0 true=Geometry.b2176 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2176

theorem bound1551 : BoxMajorant Geometry.b1551 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1551 2 (by decide +kernel) x hx hd ho).elim

theorem bound1106 : BoxMajorant Geometry.b1106 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1106.Widths)
  · have he : Geometry.b1106.half 2 false=Geometry.b1553 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1553
  · have he : Geometry.b1106.half 2 true=Geometry.b1554 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1554

theorem bound1105 : BoxMajorant Geometry.b1105 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1105.Widths)
  · have he : Geometry.b1105.half 2 false=Geometry.b1551 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1551
  · have he : Geometry.b1105.half 2 true=Geometry.b1552 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1552

theorem bound804 : BoxMajorant Geometry.b804 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b804.Widths)
  · have he : Geometry.b804.half 1 false=Geometry.b1105 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1105
  · have he : Geometry.b804.half 1 true=Geometry.b1106 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1106

end N7.Kernel.Cover
