import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverProofs.P0186
import N7.Kernel.CoverProofs.P0187
import N7.Kernel.CoverProofs.P0188
import N7.Kernel.CoverProofs.P0189
import N7.Kernel.CoverProofs.P0190
import N7.Kernel.CoverProofs.P0191
import N7.Kernel.CoverProofs.P0192
import N7.Kernel.CoverProofs.P0193
import N7.Kernel.PositiveGroups.G0190
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3183 : BoxMajorant Geometry.b3183 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3183 2 (by decide +kernel) x hx hd ho).elim

theorem bound2807 : BoxMajorant Geometry.b2807 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2807 2 (by decide +kernel) x hx hd ho).elim

theorem bound2805 : BoxMajorant Geometry.b2805 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2805 2 (by decide +kernel) x hx hd ho).elim

theorem bound2803 : BoxMajorant Geometry.b2803 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2803 2 (by decide +kernel) x hx hd ho).elim

theorem bound2801 : BoxMajorant Geometry.b2801 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2801 2 (by decide +kernel) x hx hd ho).elim

theorem bound2799 : BoxMajorant Geometry.b2799 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2799 2 (by decide +kernel) x hx hd ho).elim

theorem bound2798 : BoxMajorant Geometry.b2798 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2798.Widths)
  · have he : Geometry.b2798.half 0 false=Geometry.b3183 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3183
  · have he : Geometry.b2798.half 0 true=Geometry.b3184 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3184

theorem bound2797 : BoxMajorant Geometry.b2797 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2797 2 (by decide +kernel) x hx hd ho).elim

theorem bound2466 : BoxMajorant Geometry.b2466 := by
  exact PositiveLeaves.L2720.bound

theorem bound2465 : BoxMajorant Geometry.b2465 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2465.Widths)
  · have he : Geometry.b2465.half 2 false=Geometry.b2809 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2809
  · have he : Geometry.b2465.half 2 true=Geometry.b2810 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2810

theorem bound2464 : BoxMajorant Geometry.b2464 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2464.Widths)
  · have he : Geometry.b2464.half 2 false=Geometry.b2807 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2807
  · have he : Geometry.b2464.half 2 true=Geometry.b2808 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2808

theorem bound2463 : BoxMajorant Geometry.b2463 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2463.Widths)
  · have he : Geometry.b2463.half 2 false=Geometry.b2805 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2805
  · have he : Geometry.b2463.half 2 true=Geometry.b2806 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2806

theorem bound2462 : BoxMajorant Geometry.b2462 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2462.Widths)
  · have he : Geometry.b2462.half 2 false=Geometry.b2803 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2803
  · have he : Geometry.b2462.half 2 true=Geometry.b2804 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2804

theorem bound2461 : BoxMajorant Geometry.b2461 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2461.Widths)
  · have he : Geometry.b2461.half 2 false=Geometry.b2801 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2801
  · have he : Geometry.b2461.half 2 true=Geometry.b2802 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2802

theorem bound2460 : BoxMajorant Geometry.b2460 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2460.Widths)
  · have he : Geometry.b2460.half 2 false=Geometry.b2799 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2799
  · have he : Geometry.b2460.half 2 true=Geometry.b2800 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2800

theorem bound2459 : BoxMajorant Geometry.b2459 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2459 2 (by decide +kernel) x hx hd ho).elim

theorem bound2458 : BoxMajorant Geometry.b2458 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2458.Widths)
  · have he : Geometry.b2458.half 2 false=Geometry.b2797 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2797
  · have he : Geometry.b2458.half 2 true=Geometry.b2798 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2798

theorem bound2457 : BoxMajorant Geometry.b2457 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2457 2 (by decide +kernel) x hx hd ho).elim

theorem bound2110 : BoxMajorant Geometry.b2110 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2110.Widths)
  · have he : Geometry.b2110.half 1 false=Geometry.b2465 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2465
  · have he : Geometry.b2110.half 1 true=Geometry.b2466 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2466

theorem bound2109 : BoxMajorant Geometry.b2109 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2109.Widths)
  · have he : Geometry.b2109.half 1 false=Geometry.b2463 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2463
  · have he : Geometry.b2109.half 1 true=Geometry.b2464 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2464

theorem bound2108 : BoxMajorant Geometry.b2108 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2108.Widths)
  · have he : Geometry.b2108.half 1 false=Geometry.b2461 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2461
  · have he : Geometry.b2108.half 1 true=Geometry.b2462 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2462

theorem bound2107 : BoxMajorant Geometry.b2107 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2107.Widths)
  · have he : Geometry.b2107.half 1 false=Geometry.b2459 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2459
  · have he : Geometry.b2107.half 1 true=Geometry.b2460 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2460

theorem bound2106 : BoxMajorant Geometry.b2106 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2106.Widths)
  · have he : Geometry.b2106.half 1 false=Geometry.b2457 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2457
  · have he : Geometry.b2106.half 1 true=Geometry.b2458 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2458

theorem bound2105 : BoxMajorant Geometry.b2105 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2105 2 (by decide +kernel) x hx hd ho).elim

theorem bound1462 : BoxMajorant Geometry.b1462 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1462.Widths)
  · have he : Geometry.b1462.half 0 false=Geometry.b2109 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2109
  · have he : Geometry.b1462.half 0 true=Geometry.b2110 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2110

theorem bound1461 : BoxMajorant Geometry.b1461 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1461 2 (by decide +kernel) x hx hd ho).elim

theorem bound1460 : BoxMajorant Geometry.b1460 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1460.Widths)
  · have he : Geometry.b1460.half 0 false=Geometry.b2107 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2107
  · have he : Geometry.b1460.half 0 true=Geometry.b2108 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2108

theorem bound1459 : BoxMajorant Geometry.b1459 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1459 2 (by decide +kernel) x hx hd ho).elim

theorem bound1458 : BoxMajorant Geometry.b1458 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1458.Widths)
  · have he : Geometry.b1458.half 0 false=Geometry.b2105 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2105
  · have he : Geometry.b1458.half 0 true=Geometry.b2106 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2106

theorem bound1457 : BoxMajorant Geometry.b1457 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1457 2 (by decide +kernel) x hx hd ho).elim

theorem bound1042 : BoxMajorant Geometry.b1042 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1042.Widths)
  · have he : Geometry.b1042.half 2 false=Geometry.b1461 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1461
  · have he : Geometry.b1042.half 2 true=Geometry.b1462 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1462

theorem bound1041 : BoxMajorant Geometry.b1041 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1041.Widths)
  · have he : Geometry.b1041.half 2 false=Geometry.b1459 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1459
  · have he : Geometry.b1041.half 2 true=Geometry.b1460 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1460

theorem bound1040 : BoxMajorant Geometry.b1040 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1040.Widths)
  · have he : Geometry.b1040.half 2 false=Geometry.b1457 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1457
  · have he : Geometry.b1040.half 2 true=Geometry.b1458 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1458

theorem bound1039 : BoxMajorant Geometry.b1039 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1039 2 (by decide +kernel) x hx hd ho).elim

theorem bound756 : BoxMajorant Geometry.b756 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b756.Widths)
  · have he : Geometry.b756.half 1 false=Geometry.b1041 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1041
  · have he : Geometry.b756.half 1 true=Geometry.b1042 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1042

theorem bound755 : BoxMajorant Geometry.b755 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b755.Widths)
  · have he : Geometry.b755.half 1 false=Geometry.b1039 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1039
  · have he : Geometry.b755.half 1 true=Geometry.b1040 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1040

theorem bound485 : BoxMajorant Geometry.b485 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b485.Widths)
  · have he : Geometry.b485.half 0 false=Geometry.b755 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound755
  · have he : Geometry.b485.half 0 true=Geometry.b756 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound756

end N7.Kernel.Cover
