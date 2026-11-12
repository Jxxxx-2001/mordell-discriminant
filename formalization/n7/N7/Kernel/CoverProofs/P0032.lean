import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverProofs.P0198
import N7.Kernel.CoverProofs.P0199
import N7.Kernel.CoverProofs.P0200
import N7.Kernel.CoverProofs.P0201
import N7.Kernel.CoverProofs.P0202
import N7.Kernel.CoverProofs.P0203
import N7.Kernel.PositiveGroups.G0075
import N7.Kernel.PositiveGroups.G0076
import N7.Kernel.PositiveGroups.G0111
import N7.Kernel.PositiveGroups.G0112
import N7.Kernel.PositiveGroups.G0186
import N7.Kernel.PositiveGroups.G0229
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2842 : BoxMajorant Geometry.b2842 := by
  exact PositiveLeaves.L2571.bound

theorem bound2841 : BoxMajorant Geometry.b2841 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2841 2 (by decide +kernel) x hx hd ho).elim

theorem bound2840 : BoxMajorant Geometry.b2840 := by
  exact PositiveLeaves.L2573.bound

theorem bound2839 : BoxMajorant Geometry.b2839 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2839 2 (by decide +kernel) x hx hd ho).elim

theorem bound2838 : BoxMajorant Geometry.b2838 := by
  exact PositiveLeaves.L2577.bound

theorem bound2836 : BoxMajorant Geometry.b2836 := by
  exact PositiveLeaves.L2582.bound

theorem bound2831 : BoxMajorant Geometry.b2831 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2831 2 (by decide +kernel) x hx hd ho).elim

theorem bound2491 : BoxMajorant Geometry.b2491 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2491 0 (by decide +kernel) x hx hd ho).elim

theorem bound2490 : BoxMajorant Geometry.b2490 := by
  exact PositiveLeaves.L2570.bound

theorem bound2489 : BoxMajorant Geometry.b2489 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2489.Widths)
  · have he : Geometry.b2489.half 2 false=Geometry.b2841 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2841
  · have he : Geometry.b2489.half 2 true=Geometry.b2842 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2842

theorem bound2488 : BoxMajorant Geometry.b2488 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2488.Widths)
  · have he : Geometry.b2488.half 2 false=Geometry.b2839 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2839
  · have he : Geometry.b2488.half 2 true=Geometry.b2840 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2840

theorem bound2487 : BoxMajorant Geometry.b2487 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2487 2 (by decide +kernel) x hx hd ho).elim

theorem bound2486 : BoxMajorant Geometry.b2486 := by
  exact PositiveLeaves.L2576.bound

theorem bound2485 : BoxMajorant Geometry.b2485 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2485.Widths)
  · have he : Geometry.b2485.half 2 false=Geometry.b2837 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2837
  · have he : Geometry.b2485.half 2 true=Geometry.b2838 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2838

theorem bound2484 : BoxMajorant Geometry.b2484 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2484.Widths)
  · have he : Geometry.b2484.half 2 false=Geometry.b2835 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2835
  · have he : Geometry.b2484.half 2 true=Geometry.b2836 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2836

theorem bound2483 : BoxMajorant Geometry.b2483 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2483.Widths)
  · have he : Geometry.b2483.half 2 false=Geometry.b2833 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2833
  · have he : Geometry.b2483.half 2 true=Geometry.b2834 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2834

theorem bound2482 : BoxMajorant Geometry.b2482 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2482.Widths)
  · have he : Geometry.b2482.half 2 false=Geometry.b2831 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2831
  · have he : Geometry.b2482.half 2 true=Geometry.b2832 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2832

theorem bound2481 : BoxMajorant Geometry.b2481 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2481 2 (by decide +kernel) x hx hd ho).elim

theorem bound2130 : BoxMajorant Geometry.b2130 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2130 0 (by decide +kernel) x hx hd ho).elim

theorem bound2129 : BoxMajorant Geometry.b2129 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2129.Widths)
  · have he : Geometry.b2129.half 1 false=Geometry.b2491 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2491
  · have he : Geometry.b2129.half 1 true=Geometry.b2492 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2492

theorem bound2128 : BoxMajorant Geometry.b2128 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2128.Widths)
  · have he : Geometry.b2128.half 1 false=Geometry.b2489 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2489
  · have he : Geometry.b2128.half 1 true=Geometry.b2490 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2490

theorem bound2127 : BoxMajorant Geometry.b2127 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2127.Widths)
  · have he : Geometry.b2127.half 1 false=Geometry.b2487 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2487
  · have he : Geometry.b2127.half 1 true=Geometry.b2488 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2488

theorem bound2126 : BoxMajorant Geometry.b2126 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2126.Widths)
  · have he : Geometry.b2126.half 1 false=Geometry.b2485 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2485
  · have he : Geometry.b2126.half 1 true=Geometry.b2486 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2486

theorem bound2125 : BoxMajorant Geometry.b2125 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2125.Widths)
  · have he : Geometry.b2125.half 1 false=Geometry.b2483 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2483
  · have he : Geometry.b2125.half 1 true=Geometry.b2484 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2484

theorem bound2124 : BoxMajorant Geometry.b2124 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2124.Widths)
  · have he : Geometry.b2124.half 1 false=Geometry.b2481 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2481
  · have he : Geometry.b2124.half 1 true=Geometry.b2482 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2482

theorem bound2123 : BoxMajorant Geometry.b2123 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2123 2 (by decide +kernel) x hx hd ho).elim

theorem bound1480 : BoxMajorant Geometry.b1480 := by
  exact PositiveLeaves.L2564.bound

theorem bound1479 : BoxMajorant Geometry.b1479 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1479.Widths)
  · have he : Geometry.b1479.half 0 false=Geometry.b2129 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2129
  · have he : Geometry.b1479.half 0 true=Geometry.b2130 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2130

theorem bound1478 : BoxMajorant Geometry.b1478 := by
  exact PositiveLeaves.L2569.bound

theorem bound1477 : BoxMajorant Geometry.b1477 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1477.Widths)
  · have he : Geometry.b1477.half 0 false=Geometry.b2127 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2127
  · have he : Geometry.b1477.half 0 true=Geometry.b2128 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2128

theorem bound1476 : BoxMajorant Geometry.b1476 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1476.Widths)
  · have he : Geometry.b1476.half 0 false=Geometry.b2125 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2125
  · have he : Geometry.b1476.half 0 true=Geometry.b2126 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2126

theorem bound1475 : BoxMajorant Geometry.b1475 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1475.Widths)
  · have he : Geometry.b1475.half 0 false=Geometry.b2123 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2123
  · have he : Geometry.b1475.half 0 true=Geometry.b2124 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2124

theorem bound1054 : BoxMajorant Geometry.b1054 := by
  exact PositiveLeaves.L2563.bound

theorem bound1053 : BoxMajorant Geometry.b1053 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1053.Widths)
  · have he : Geometry.b1053.half 2 false=Geometry.b1479 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1479
  · have he : Geometry.b1053.half 2 true=Geometry.b1480 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1480

theorem bound1052 : BoxMajorant Geometry.b1052 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1052.Widths)
  · have he : Geometry.b1052.half 2 false=Geometry.b1477 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1477
  · have he : Geometry.b1052.half 2 true=Geometry.b1478 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1478

theorem bound1051 : BoxMajorant Geometry.b1051 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1051.Widths)
  · have he : Geometry.b1051.half 2 false=Geometry.b1475 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1475
  · have he : Geometry.b1051.half 2 true=Geometry.b1476 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1476

theorem bound764 : BoxMajorant Geometry.b764 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b764.Widths)
  · have he : Geometry.b764.half 1 false=Geometry.b1053 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1053
  · have he : Geometry.b764.half 1 true=Geometry.b1054 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1054

theorem bound763 : BoxMajorant Geometry.b763 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b763.Widths)
  · have he : Geometry.b763.half 1 false=Geometry.b1051 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1051
  · have he : Geometry.b763.half 1 true=Geometry.b1052 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1052

theorem bound489 : BoxMajorant Geometry.b489 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b489.Widths)
  · have he : Geometry.b489.half 0 false=Geometry.b763 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound763
  · have he : Geometry.b489.half 0 true=Geometry.b764 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound764

end N7.Kernel.Cover
