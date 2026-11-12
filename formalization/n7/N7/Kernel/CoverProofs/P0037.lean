import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverProofs.P0204
import N7.Kernel.CoverProofs.P0205
import N7.Kernel.CoverProofs.P0206
import N7.Kernel.PositiveGroups.G0106
import N7.Kernel.PositiveGroups.G0107
import N7.Kernel.PositiveGroups.G0147
import N7.Kernel.PositiveGroups.G0184
import N7.Kernel.PositiveGroups.G0185
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2860 : BoxMajorant Geometry.b2860 := by
  exact PositiveLeaves.L2501.bound

theorem bound2858 : BoxMajorant Geometry.b2858 := by
  exact PositiveLeaves.L2504.bound

theorem bound2857 : BoxMajorant Geometry.b2857 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2857 2 (by decide +kernel) x hx hd ho).elim

theorem bound2856 : BoxMajorant Geometry.b2856 := by
  exact PositiveLeaves.L2506.bound

theorem bound2855 : BoxMajorant Geometry.b2855 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2855 2 (by decide +kernel) x hx hd ho).elim

theorem bound2853 : BoxMajorant Geometry.b2853 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2853 2 (by decide +kernel) x hx hd ho).elim

theorem bound2851 : BoxMajorant Geometry.b2851 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2851 2 (by decide +kernel) x hx hd ho).elim

theorem bound2508 : BoxMajorant Geometry.b2508 := by
  exact PositiveLeaves.L2497.bound

theorem bound2507 : BoxMajorant Geometry.b2507 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2507 2 (by decide +kernel) x hx hd ho).elim

theorem bound2506 : BoxMajorant Geometry.b2506 := by
  exact PositiveLeaves.L2500.bound

theorem bound2505 : BoxMajorant Geometry.b2505 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2505.Widths)
  · have he : Geometry.b2505.half 2 false=Geometry.b2859 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2859
  · have he : Geometry.b2505.half 2 true=Geometry.b2860 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2860

theorem bound2504 : BoxMajorant Geometry.b2504 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2504.Widths)
  · have he : Geometry.b2504.half 2 false=Geometry.b2857 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2857
  · have he : Geometry.b2504.half 2 true=Geometry.b2858 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2858

theorem bound2503 : BoxMajorant Geometry.b2503 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2503.Widths)
  · have he : Geometry.b2503.half 2 false=Geometry.b2855 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2855
  · have he : Geometry.b2503.half 2 true=Geometry.b2856 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2856

theorem bound2502 : BoxMajorant Geometry.b2502 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2502.Widths)
  · have he : Geometry.b2502.half 2 false=Geometry.b2853 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2853
  · have he : Geometry.b2502.half 2 true=Geometry.b2854 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2854

theorem bound2501 : BoxMajorant Geometry.b2501 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2501.Widths)
  · have he : Geometry.b2501.half 2 false=Geometry.b2851 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2851
  · have he : Geometry.b2501.half 2 true=Geometry.b2852 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2852

theorem bound2152 : BoxMajorant Geometry.b2152 := by
  exact PositiveLeaves.L2496.bound

theorem bound2151 : BoxMajorant Geometry.b2151 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2151.Widths)
  · have he : Geometry.b2151.half 1 false=Geometry.b2507 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2507
  · have he : Geometry.b2151.half 1 true=Geometry.b2508 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2508

theorem bound2150 : BoxMajorant Geometry.b2150 := by
  exact PositiveLeaves.L2499.bound

theorem bound2149 : BoxMajorant Geometry.b2149 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2149.Widths)
  · have he : Geometry.b2149.half 1 false=Geometry.b2505 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2505
  · have he : Geometry.b2149.half 1 true=Geometry.b2506 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2506

theorem bound2148 : BoxMajorant Geometry.b2148 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2148.Widths)
  · have he : Geometry.b2148.half 1 false=Geometry.b2503 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2503
  · have he : Geometry.b2148.half 1 true=Geometry.b2504 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2504

theorem bound2147 : BoxMajorant Geometry.b2147 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2147 2 (by decide +kernel) x hx hd ho).elim

theorem bound2146 : BoxMajorant Geometry.b2146 := by
  exact PositiveLeaves.L2509.bound

theorem bound2145 : BoxMajorant Geometry.b2145 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2145 2 (by decide +kernel) x hx hd ho).elim

theorem bound2144 : BoxMajorant Geometry.b2144 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2144.Widths)
  · have he : Geometry.b2144.half 1 false=Geometry.b2501 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2501
  · have he : Geometry.b2144.half 1 true=Geometry.b2502 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2502

theorem bound2143 : BoxMajorant Geometry.b2143 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2143 2 (by decide +kernel) x hx hd ho).elim

theorem bound1508 : BoxMajorant Geometry.b1508 := by
  exact PositiveLeaves.L2495.bound

theorem bound1507 : BoxMajorant Geometry.b1507 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1507.Widths)
  · have he : Geometry.b1507.half 0 false=Geometry.b2151 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2151
  · have he : Geometry.b1507.half 0 true=Geometry.b2152 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2152

theorem bound1506 : BoxMajorant Geometry.b1506 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1506.Widths)
  · have he : Geometry.b1506.half 0 false=Geometry.b2149 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2149
  · have he : Geometry.b1506.half 0 true=Geometry.b2150 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2150

theorem bound1505 : BoxMajorant Geometry.b1505 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1505.Widths)
  · have he : Geometry.b1505.half 0 false=Geometry.b2147 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2147
  · have he : Geometry.b1505.half 0 true=Geometry.b2148 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2148

theorem bound1504 : BoxMajorant Geometry.b1504 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1504.Widths)
  · have he : Geometry.b1504.half 0 false=Geometry.b2145 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2145
  · have he : Geometry.b1504.half 0 true=Geometry.b2146 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2146

theorem bound1503 : BoxMajorant Geometry.b1503 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1503 2 (by decide +kernel) x hx hd ho).elim

theorem bound1502 : BoxMajorant Geometry.b1502 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1502.Widths)
  · have he : Geometry.b1502.half 0 false=Geometry.b2143 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2143
  · have he : Geometry.b1502.half 0 true=Geometry.b2144 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2144

theorem bound1501 : BoxMajorant Geometry.b1501 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1501 2 (by decide +kernel) x hx hd ho).elim

theorem bound1070 : BoxMajorant Geometry.b1070 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1070.Widths)
  · have he : Geometry.b1070.half 2 false=Geometry.b1507 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1507
  · have he : Geometry.b1070.half 2 true=Geometry.b1508 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1508

theorem bound1069 : BoxMajorant Geometry.b1069 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1069.Widths)
  · have he : Geometry.b1069.half 2 false=Geometry.b1505 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1505
  · have he : Geometry.b1069.half 2 true=Geometry.b1506 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1506

theorem bound1068 : BoxMajorant Geometry.b1068 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1068.Widths)
  · have he : Geometry.b1068.half 2 false=Geometry.b1503 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1503
  · have he : Geometry.b1068.half 2 true=Geometry.b1504 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1504

theorem bound1067 : BoxMajorant Geometry.b1067 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1067.Widths)
  · have he : Geometry.b1067.half 2 false=Geometry.b1501 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1501
  · have he : Geometry.b1067.half 2 true=Geometry.b1502 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1502

theorem bound774 : BoxMajorant Geometry.b774 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b774.Widths)
  · have he : Geometry.b774.half 1 false=Geometry.b1069 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1069
  · have he : Geometry.b774.half 1 true=Geometry.b1070 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1070

theorem bound773 : BoxMajorant Geometry.b773 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b773.Widths)
  · have he : Geometry.b773.half 1 false=Geometry.b1067 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1067
  · have he : Geometry.b773.half 1 true=Geometry.b1068 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1068

theorem bound497 : BoxMajorant Geometry.b497 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b497.Widths)
  · have he : Geometry.b497.half 0 false=Geometry.b773 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound773
  · have he : Geometry.b497.half 0 true=Geometry.b774 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound774

end N7.Kernel.Cover
