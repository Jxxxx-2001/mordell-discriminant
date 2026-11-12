import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverProofs.P0215
import N7.Kernel.CoverProofs.P0216
import N7.Kernel.CoverProofs.P0217
import N7.Kernel.CoverProofs.P0218
import N7.Kernel.CoverProofs.P0219
import N7.Kernel.CoverProofs.P0220
import N7.Kernel.CoverProofs.P0221
import N7.Kernel.CoverProofs.P0222
import N7.Kernel.PositiveGroups.G0145
import N7.Kernel.PositiveGroups.G0227
import N7.Kernel.PositiveGroups.G0265
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3249 : BoxMajorant Geometry.b3249 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3249 2 (by decide +kernel) x hx hd ho).elim

theorem bound3248 : BoxMajorant Geometry.b3248 := by
  exact PositiveLeaves.L2158.bound

theorem bound3247 : BoxMajorant Geometry.b3247 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3247 2 (by decide +kernel) x hx hd ho).elim

theorem bound2936 : BoxMajorant Geometry.b2936 := by
  exact PositiveLeaves.L2100.bound

theorem bound2929 : BoxMajorant Geometry.b2929 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2929 2 (by decide +kernel) x hx hd ho).elim

theorem bound2927 : BoxMajorant Geometry.b2927 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2927 2 (by decide +kernel) x hx hd ho).elim

theorem bound2926 : BoxMajorant Geometry.b2926 := by
  exact PositiveLeaves.L2149.bound

theorem bound2925 : BoxMajorant Geometry.b2925 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2925 2 (by decide +kernel) x hx hd ho).elim

theorem bound2924 : BoxMajorant Geometry.b2924 := by
  exact PositiveLeaves.L2151.bound

theorem bound2923 : BoxMajorant Geometry.b2923 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2923 2 (by decide +kernel) x hx hd ho).elim

theorem bound2922 : BoxMajorant Geometry.b2922 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2922.Widths)
  · have he : Geometry.b2922.half 0 false=Geometry.b3249 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3249
  · have he : Geometry.b2922.half 0 true=Geometry.b3250 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3250

theorem bound2921 : BoxMajorant Geometry.b2921 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2921 2 (by decide +kernel) x hx hd ho).elim

theorem bound2920 : BoxMajorant Geometry.b2920 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2920.Widths)
  · have he : Geometry.b2920.half 0 false=Geometry.b3247 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3247
  · have he : Geometry.b2920.half 0 true=Geometry.b3248 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3248

theorem bound2919 : BoxMajorant Geometry.b2919 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2919 2 (by decide +kernel) x hx hd ho).elim

theorem bound2580 : BoxMajorant Geometry.b2580 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2580.Widths)
  · have he : Geometry.b2580.half 2 false=Geometry.b2935 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2935
  · have he : Geometry.b2580.half 2 true=Geometry.b2936 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2936

theorem bound2579 : BoxMajorant Geometry.b2579 := by
  exact PositiveLeaves.L2110.bound

theorem bound2578 : BoxMajorant Geometry.b2578 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2578.Widths)
  · have he : Geometry.b2578.half 2 false=Geometry.b2933 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2933
  · have he : Geometry.b2578.half 2 true=Geometry.b2934 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2934

theorem bound2577 : BoxMajorant Geometry.b2577 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2577.Widths)
  · have he : Geometry.b2577.half 2 false=Geometry.b2931 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2931
  · have he : Geometry.b2577.half 2 true=Geometry.b2932 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2932

theorem bound2576 : BoxMajorant Geometry.b2576 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2576.Widths)
  · have he : Geometry.b2576.half 2 false=Geometry.b2929 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2929
  · have he : Geometry.b2576.half 2 true=Geometry.b2930 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2930

theorem bound2575 : BoxMajorant Geometry.b2575 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2575.Widths)
  · have he : Geometry.b2575.half 2 false=Geometry.b2927 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2927
  · have he : Geometry.b2575.half 2 true=Geometry.b2928 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2928

theorem bound2574 : BoxMajorant Geometry.b2574 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2574.Widths)
  · have he : Geometry.b2574.half 2 false=Geometry.b2925 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2925
  · have he : Geometry.b2574.half 2 true=Geometry.b2926 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2926

theorem bound2573 : BoxMajorant Geometry.b2573 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2573.Widths)
  · have he : Geometry.b2573.half 2 false=Geometry.b2923 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2923
  · have he : Geometry.b2573.half 2 true=Geometry.b2924 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2924

theorem bound2572 : BoxMajorant Geometry.b2572 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2572.Widths)
  · have he : Geometry.b2572.half 2 false=Geometry.b2921 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2921
  · have he : Geometry.b2572.half 2 true=Geometry.b2922 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2922

theorem bound2571 : BoxMajorant Geometry.b2571 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2571.Widths)
  · have he : Geometry.b2571.half 2 false=Geometry.b2919 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2919
  · have he : Geometry.b2571.half 2 true=Geometry.b2920 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2920

theorem bound2216 : BoxMajorant Geometry.b2216 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2216.Widths)
  · have he : Geometry.b2216.half 1 false=Geometry.b2579 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2579
  · have he : Geometry.b2216.half 1 true=Geometry.b2580 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2580

theorem bound2215 : BoxMajorant Geometry.b2215 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2215.Widths)
  · have he : Geometry.b2215.half 1 false=Geometry.b2577 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2577
  · have he : Geometry.b2215.half 1 true=Geometry.b2578 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2578

theorem bound2214 : BoxMajorant Geometry.b2214 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2214.Widths)
  · have he : Geometry.b2214.half 1 false=Geometry.b2575 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2575
  · have he : Geometry.b2214.half 1 true=Geometry.b2576 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2576

theorem bound2213 : BoxMajorant Geometry.b2213 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2213 2 (by decide +kernel) x hx hd ho).elim

theorem bound2212 : BoxMajorant Geometry.b2212 := by
  exact PositiveLeaves.L2148.bound

theorem bound2211 : BoxMajorant Geometry.b2211 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2211.Widths)
  · have he : Geometry.b2211.half 1 false=Geometry.b2573 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2573
  · have he : Geometry.b2211.half 1 true=Geometry.b2574 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2574

theorem bound2210 : BoxMajorant Geometry.b2210 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2210.Widths)
  · have he : Geometry.b2210.half 1 false=Geometry.b2571 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2571
  · have he : Geometry.b2210.half 1 true=Geometry.b2572 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2572

theorem bound2209 : BoxMajorant Geometry.b2209 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2209 2 (by decide +kernel) x hx hd ho).elim

theorem bound1608 : BoxMajorant Geometry.b1608 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1608.Widths)
  · have he : Geometry.b1608.half 0 false=Geometry.b2215 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2215
  · have he : Geometry.b1608.half 0 true=Geometry.b2216 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2216

theorem bound1607 : BoxMajorant Geometry.b1607 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1607.Widths)
  · have he : Geometry.b1607.half 0 false=Geometry.b2213 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2213
  · have he : Geometry.b1607.half 0 true=Geometry.b2214 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2214

theorem bound1606 : BoxMajorant Geometry.b1606 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1606.Widths)
  · have he : Geometry.b1606.half 0 false=Geometry.b2211 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2211
  · have he : Geometry.b1606.half 0 true=Geometry.b2212 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2212

theorem bound1605 : BoxMajorant Geometry.b1605 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1605.Widths)
  · have he : Geometry.b1605.half 0 false=Geometry.b2209 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2209
  · have he : Geometry.b1605.half 0 true=Geometry.b2210 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2210

theorem bound1140 : BoxMajorant Geometry.b1140 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1140.Widths)
  · have he : Geometry.b1140.half 2 false=Geometry.b1607 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1607
  · have he : Geometry.b1140.half 2 true=Geometry.b1608 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1608

theorem bound1139 : BoxMajorant Geometry.b1139 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1139.Widths)
  · have he : Geometry.b1139.half 2 false=Geometry.b1605 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1605
  · have he : Geometry.b1139.half 2 true=Geometry.b1606 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1606

theorem bound828 : BoxMajorant Geometry.b828 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b828.Widths)
  · have he : Geometry.b828.half 1 false=Geometry.b1139 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1139
  · have he : Geometry.b828.half 1 true=Geometry.b1140 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1140

theorem bound827 : BoxMajorant Geometry.b827 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b827 2 (by decide +kernel) x hx hd ho).elim

theorem bound552 : BoxMajorant Geometry.b552 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b552.Widths)
  · have he : Geometry.b552.half 0 false=Geometry.b827 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound827
  · have he : Geometry.b552.half 0 true=Geometry.b828 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound828

end N7.Kernel.Cover
