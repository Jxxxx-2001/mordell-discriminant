import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverProofs.P0194
import N7.Kernel.CoverProofs.P0195
import N7.Kernel.CoverProofs.P0196
import N7.Kernel.CoverProofs.P0197
import N7.Kernel.PositiveGroups.G0076
import N7.Kernel.PositiveGroups.G0112
import N7.Kernel.PositiveGroups.G0113
import N7.Kernel.PositiveGroups.G0152
import N7.Kernel.PositiveGroups.G0188
import N7.Kernel.PositiveGroups.G0189
import N7.Kernel.PositiveGroups.G0190
import N7.Kernel.PositiveGroups.G0231
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2826 : BoxMajorant Geometry.b2826 := by
  exact PositiveLeaves.L2674.bound

theorem bound2824 : BoxMajorant Geometry.b2824 := by
  exact PositiveLeaves.L2685.bound

theorem bound2822 : BoxMajorant Geometry.b2822 := by
  exact PositiveLeaves.L2701.bound

theorem bound2821 : BoxMajorant Geometry.b2821 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2821 2 (by decide +kernel) x hx hd ho).elim

theorem bound2820 : BoxMajorant Geometry.b2820 := by
  exact PositiveLeaves.L2703.bound

theorem bound2819 : BoxMajorant Geometry.b2819 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2819 2 (by decide +kernel) x hx hd ho).elim

theorem bound2818 : BoxMajorant Geometry.b2818 := by
  exact PositiveLeaves.L2706.bound

theorem bound2816 : BoxMajorant Geometry.b2816 := by
  exact PositiveLeaves.L2714.bound

theorem bound2815 : BoxMajorant Geometry.b2815 := by
  exact PositiveLeaves.L2715.bound

theorem bound2814 : BoxMajorant Geometry.b2814 := by
  exact PositiveLeaves.L2716.bound

theorem bound2813 : BoxMajorant Geometry.b2813 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2813 2 (by decide +kernel) x hx hd ho).elim

theorem bound2812 : BoxMajorant Geometry.b2812 := by
  exact PositiveLeaves.L2718.bound

theorem bound2811 : BoxMajorant Geometry.b2811 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2811 2 (by decide +kernel) x hx hd ho).elim

theorem bound2478 : BoxMajorant Geometry.b2478 := by
  exact PositiveLeaves.L2664.bound

theorem bound2477 : BoxMajorant Geometry.b2477 := by
  exact PositiveLeaves.L2665.bound

theorem bound2475 : BoxMajorant Geometry.b2475 := by
  exact PositiveLeaves.L2672.bound

theorem bound2474 : BoxMajorant Geometry.b2474 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2474.Widths)
  · have he : Geometry.b2474.half 2 false=Geometry.b2825 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2825
  · have he : Geometry.b2474.half 2 true=Geometry.b2826 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2826

theorem bound2473 : BoxMajorant Geometry.b2473 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2473.Widths)
  · have he : Geometry.b2473.half 2 false=Geometry.b2823 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2823
  · have he : Geometry.b2473.half 2 true=Geometry.b2824 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2824

theorem bound2472 : BoxMajorant Geometry.b2472 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2472.Widths)
  · have he : Geometry.b2472.half 2 false=Geometry.b2821 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2821
  · have he : Geometry.b2472.half 2 true=Geometry.b2822 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2822

theorem bound2471 : BoxMajorant Geometry.b2471 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2471.Widths)
  · have he : Geometry.b2471.half 2 false=Geometry.b2819 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2819
  · have he : Geometry.b2471.half 2 true=Geometry.b2820 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2820

theorem bound2470 : BoxMajorant Geometry.b2470 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2470.Widths)
  · have he : Geometry.b2470.half 2 false=Geometry.b2817 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2817
  · have he : Geometry.b2470.half 2 true=Geometry.b2818 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2818

theorem bound2469 : BoxMajorant Geometry.b2469 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2469.Widths)
  · have he : Geometry.b2469.half 2 false=Geometry.b2815 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2815
  · have he : Geometry.b2469.half 2 true=Geometry.b2816 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2816

theorem bound2468 : BoxMajorant Geometry.b2468 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2468.Widths)
  · have he : Geometry.b2468.half 2 false=Geometry.b2813 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2813
  · have he : Geometry.b2468.half 2 true=Geometry.b2814 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2814

theorem bound2467 : BoxMajorant Geometry.b2467 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2467.Widths)
  · have he : Geometry.b2467.half 2 false=Geometry.b2811 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2811
  · have he : Geometry.b2467.half 2 true=Geometry.b2812 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2812

theorem bound2118 : BoxMajorant Geometry.b2118 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2118.Widths)
  · have he : Geometry.b2118.half 1 false=Geometry.b2477 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2477
  · have he : Geometry.b2118.half 1 true=Geometry.b2478 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2478

theorem bound2117 : BoxMajorant Geometry.b2117 := by
  exact PositiveLeaves.L2666.bound

theorem bound2116 : BoxMajorant Geometry.b2116 := by
  exact PositiveLeaves.L2669.bound

theorem bound2115 : BoxMajorant Geometry.b2115 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2115.Widths)
  · have he : Geometry.b2115.half 1 false=Geometry.b2475 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2475
  · have he : Geometry.b2115.half 1 true=Geometry.b2476 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2476

theorem bound2114 : BoxMajorant Geometry.b2114 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2114.Widths)
  · have he : Geometry.b2114.half 1 false=Geometry.b2473 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2473
  · have he : Geometry.b2114.half 1 true=Geometry.b2474 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2474

theorem bound2113 : BoxMajorant Geometry.b2113 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2113.Widths)
  · have he : Geometry.b2113.half 1 false=Geometry.b2471 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2471
  · have he : Geometry.b2113.half 1 true=Geometry.b2472 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2472

theorem bound2112 : BoxMajorant Geometry.b2112 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2112.Widths)
  · have he : Geometry.b2112.half 1 false=Geometry.b2469 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2469
  · have he : Geometry.b2112.half 1 true=Geometry.b2470 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2470

theorem bound2111 : BoxMajorant Geometry.b2111 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2111.Widths)
  · have he : Geometry.b2111.half 1 false=Geometry.b2467 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2467
  · have he : Geometry.b2111.half 1 true=Geometry.b2468 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2468

theorem bound1470 : BoxMajorant Geometry.b1470 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1470.Widths)
  · have he : Geometry.b1470.half 0 false=Geometry.b2117 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2117
  · have he : Geometry.b1470.half 0 true=Geometry.b2118 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2118

theorem bound1469 : BoxMajorant Geometry.b1469 := by
  exact PositiveLeaves.L2667.bound

theorem bound1468 : BoxMajorant Geometry.b1468 := by
  exact PositiveLeaves.L2668.bound

theorem bound1467 : BoxMajorant Geometry.b1467 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1467.Widths)
  · have he : Geometry.b1467.half 0 false=Geometry.b2115 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2115
  · have he : Geometry.b1467.half 0 true=Geometry.b2116 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2116

theorem bound1466 : BoxMajorant Geometry.b1466 := by
  exact PositiveLeaves.L2673.bound

theorem bound1465 : BoxMajorant Geometry.b1465 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1465.Widths)
  · have he : Geometry.b1465.half 0 false=Geometry.b2113 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2113
  · have he : Geometry.b1465.half 0 true=Geometry.b2114 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2114

theorem bound1464 : BoxMajorant Geometry.b1464 := by
  exact PositiveLeaves.L2705.bound

theorem bound1463 : BoxMajorant Geometry.b1463 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1463.Widths)
  · have he : Geometry.b1463.half 0 false=Geometry.b2111 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2111
  · have he : Geometry.b1463.half 0 true=Geometry.b2112 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2112

theorem bound1046 : BoxMajorant Geometry.b1046 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1046.Widths)
  · have he : Geometry.b1046.half 2 false=Geometry.b1469 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1469
  · have he : Geometry.b1046.half 2 true=Geometry.b1470 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1470

theorem bound1045 : BoxMajorant Geometry.b1045 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1045.Widths)
  · have he : Geometry.b1045.half 2 false=Geometry.b1467 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1467
  · have he : Geometry.b1045.half 2 true=Geometry.b1468 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1468

theorem bound1044 : BoxMajorant Geometry.b1044 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1044.Widths)
  · have he : Geometry.b1044.half 2 false=Geometry.b1465 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1465
  · have he : Geometry.b1044.half 2 true=Geometry.b1466 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1466

theorem bound1043 : BoxMajorant Geometry.b1043 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1043.Widths)
  · have he : Geometry.b1043.half 2 false=Geometry.b1463 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1463
  · have he : Geometry.b1043.half 2 true=Geometry.b1464 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1464

theorem bound758 : BoxMajorant Geometry.b758 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b758.Widths)
  · have he : Geometry.b758.half 1 false=Geometry.b1045 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1045
  · have he : Geometry.b758.half 1 true=Geometry.b1046 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1046

theorem bound757 : BoxMajorant Geometry.b757 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b757.Widths)
  · have he : Geometry.b757.half 1 false=Geometry.b1043 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1043
  · have he : Geometry.b757.half 1 true=Geometry.b1044 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1044

theorem bound486 : BoxMajorant Geometry.b486 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b486.Widths)
  · have he : Geometry.b486.half 0 false=Geometry.b757 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound757
  · have he : Geometry.b486.half 0 true=Geometry.b758 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound758

end N7.Kernel.Cover
