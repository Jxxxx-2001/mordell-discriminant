import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.PositiveGroups.G0112
import N7.Kernel.PositiveGroups.G0150
import N7.Kernel.PositiveGroups.G0151
import N7.Kernel.PositiveGroups.G0187
import N7.Kernel.PositiveGroups.G0229
import N7.Kernel.PositiveGroups.G0230
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2850 : BoxMajorant Geometry.b2850 := by
  exact PositiveLeaves.L2545.bound

theorem bound2849 : BoxMajorant Geometry.b2849 := by
  exact PositiveLeaves.L2546.bound

theorem bound2848 : BoxMajorant Geometry.b2848 := by
  exact PositiveLeaves.L2547.bound

theorem bound2847 : BoxMajorant Geometry.b2847 := by
  exact PositiveLeaves.L2548.bound

theorem bound2846 : BoxMajorant Geometry.b2846 := by
  exact PositiveLeaves.L2549.bound

theorem bound2845 : BoxMajorant Geometry.b2845 := by
  exact PositiveLeaves.L2550.bound

theorem bound2498 : BoxMajorant Geometry.b2498 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2498.Widths)
  · have he : Geometry.b2498.half 2 false=Geometry.b2849 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2849
  · have he : Geometry.b2498.half 2 true=Geometry.b2850 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2850

theorem bound2497 : BoxMajorant Geometry.b2497 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2497.Widths)
  · have he : Geometry.b2497.half 2 false=Geometry.b2847 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2847
  · have he : Geometry.b2497.half 2 true=Geometry.b2848 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2848

theorem bound2496 : BoxMajorant Geometry.b2496 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2496.Widths)
  · have he : Geometry.b2496.half 2 false=Geometry.b2845 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2845
  · have he : Geometry.b2496.half 2 true=Geometry.b2846 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2846

theorem bound2495 : BoxMajorant Geometry.b2495 := by
  exact PositiveLeaves.L2551.bound

theorem bound2494 : BoxMajorant Geometry.b2494 := by
  exact PositiveLeaves.L2559.bound

theorem bound2493 : BoxMajorant Geometry.b2493 := by
  exact PositiveLeaves.L2560.bound

theorem bound2138 : BoxMajorant Geometry.b2138 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2138.Widths)
  · have he : Geometry.b2138.half 1 false=Geometry.b2497 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2497
  · have he : Geometry.b2138.half 1 true=Geometry.b2498 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2498

theorem bound2137 : BoxMajorant Geometry.b2137 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2137.Widths)
  · have he : Geometry.b2137.half 1 false=Geometry.b2495 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2495
  · have he : Geometry.b2137.half 1 true=Geometry.b2496 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2496

theorem bound2136 : BoxMajorant Geometry.b2136 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2136 0 (by decide +kernel) x hx hd ho).elim

theorem bound2135 : BoxMajorant Geometry.b2135 := by
  exact PositiveLeaves.L2554.bound

theorem bound2134 : BoxMajorant Geometry.b2134 := by
  exact PositiveLeaves.L2556.bound

theorem bound2133 : BoxMajorant Geometry.b2133 := by
  exact PositiveLeaves.L2557.bound

theorem bound2132 : BoxMajorant Geometry.b2132 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2132.Widths)
  · have he : Geometry.b2132.half 1 false=Geometry.b2493 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2493
  · have he : Geometry.b2132.half 1 true=Geometry.b2494 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2494

theorem bound2131 : BoxMajorant Geometry.b2131 := by
  exact PositiveLeaves.L2561.bound

theorem bound1488 : BoxMajorant Geometry.b1488 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1488.Widths)
  · have he : Geometry.b1488.half 0 false=Geometry.b2137 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2137
  · have he : Geometry.b1488.half 0 true=Geometry.b2138 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2138

theorem bound1487 : BoxMajorant Geometry.b1487 := by
  exact PositiveLeaves.L2552.bound

theorem bound1486 : BoxMajorant Geometry.b1486 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1486.Widths)
  · have he : Geometry.b1486.half 0 false=Geometry.b2135 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2135
  · have he : Geometry.b1486.half 0 true=Geometry.b2136 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2136

theorem bound1485 : BoxMajorant Geometry.b1485 := by
  exact PositiveLeaves.L2555.bound

theorem bound1484 : BoxMajorant Geometry.b1484 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1484.Widths)
  · have he : Geometry.b1484.half 0 false=Geometry.b2133 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2133
  · have he : Geometry.b1484.half 0 true=Geometry.b2134 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2134

theorem bound1483 : BoxMajorant Geometry.b1483 := by
  exact PositiveLeaves.L2558.bound

theorem bound1482 : BoxMajorant Geometry.b1482 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1482.Widths)
  · have he : Geometry.b1482.half 0 false=Geometry.b2131 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2131
  · have he : Geometry.b1482.half 0 true=Geometry.b2132 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2132

theorem bound1481 : BoxMajorant Geometry.b1481 := by
  exact PositiveLeaves.L2562.bound

theorem bound1058 : BoxMajorant Geometry.b1058 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1058.Widths)
  · have he : Geometry.b1058.half 2 false=Geometry.b1487 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1487
  · have he : Geometry.b1058.half 2 true=Geometry.b1488 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1488

theorem bound1057 : BoxMajorant Geometry.b1057 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1057.Widths)
  · have he : Geometry.b1057.half 2 false=Geometry.b1485 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1485
  · have he : Geometry.b1057.half 2 true=Geometry.b1486 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1486

theorem bound1056 : BoxMajorant Geometry.b1056 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1056.Widths)
  · have he : Geometry.b1056.half 2 false=Geometry.b1483 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1483
  · have he : Geometry.b1056.half 2 true=Geometry.b1484 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1484

theorem bound1055 : BoxMajorant Geometry.b1055 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1055.Widths)
  · have he : Geometry.b1055.half 2 false=Geometry.b1481 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1481
  · have he : Geometry.b1055.half 2 true=Geometry.b1482 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1482

theorem bound766 : BoxMajorant Geometry.b766 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b766.Widths)
  · have he : Geometry.b766.half 1 false=Geometry.b1057 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1057
  · have he : Geometry.b766.half 1 true=Geometry.b1058 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1058

theorem bound765 : BoxMajorant Geometry.b765 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b765.Widths)
  · have he : Geometry.b765.half 1 false=Geometry.b1055 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1055
  · have he : Geometry.b765.half 1 true=Geometry.b1056 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1056

theorem bound490 : BoxMajorant Geometry.b490 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b490.Widths)
  · have he : Geometry.b490.half 0 false=Geometry.b765 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound765
  · have he : Geometry.b490.half 0 true=Geometry.b766 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound766

end N7.Kernel.Cover
