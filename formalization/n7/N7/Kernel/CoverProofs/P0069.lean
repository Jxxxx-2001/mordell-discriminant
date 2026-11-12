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
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverProofs.P0223
import N7.Kernel.CoverProofs.P0224
import N7.Kernel.CoverProofs.P0225
import N7.Kernel.CoverProofs.P0226
import N7.Kernel.CoverProofs.P0227
import N7.Kernel.CoverProofs.P0228
import N7.Kernel.CoverProofs.P0229
import N7.Kernel.CoverProofs.P0230
import N7.Kernel.CoverProofs.P0231
import N7.Kernel.CoverProofs.P0232
import N7.Kernel.CoverProofs.P0233
import N7.Kernel.CoverProofs.P0234
import N7.Kernel.CoverProofs.P0235
import N7.Kernel.PositiveGroups.G0183
import N7.Kernel.PositiveGroups.G0226
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2950 : BoxMajorant Geometry.b2950 := by
  exact PositiveLeaves.L1983.bound

theorem bound2948 : BoxMajorant Geometry.b2948 := by
  exact PositiveLeaves.L1992.bound

theorem bound2941 : BoxMajorant Geometry.b2941 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2941 2 (by decide +kernel) x hx hd ho).elim

theorem bound2939 : BoxMajorant Geometry.b2939 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2939 2 (by decide +kernel) x hx hd ho).elim

theorem bound2937 : BoxMajorant Geometry.b2937 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2937 2 (by decide +kernel) x hx hd ho).elim

theorem bound2588 : BoxMajorant Geometry.b2588 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2588.Widths)
  · have he : Geometry.b2588.half 2 false=Geometry.b2949 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2949
  · have he : Geometry.b2588.half 2 true=Geometry.b2950 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2950

theorem bound2587 : BoxMajorant Geometry.b2587 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2587.Widths)
  · have he : Geometry.b2587.half 2 false=Geometry.b2947 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2947
  · have he : Geometry.b2587.half 2 true=Geometry.b2948 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2948

theorem bound2586 : BoxMajorant Geometry.b2586 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2586.Widths)
  · have he : Geometry.b2586.half 2 false=Geometry.b2945 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2945
  · have he : Geometry.b2586.half 2 true=Geometry.b2946 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2946

theorem bound2585 : BoxMajorant Geometry.b2585 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2585.Widths)
  · have he : Geometry.b2585.half 2 false=Geometry.b2943 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2943
  · have he : Geometry.b2585.half 2 true=Geometry.b2944 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2944

theorem bound2584 : BoxMajorant Geometry.b2584 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2584.Widths)
  · have he : Geometry.b2584.half 2 false=Geometry.b2941 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2941
  · have he : Geometry.b2584.half 2 true=Geometry.b2942 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2942

theorem bound2583 : BoxMajorant Geometry.b2583 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2583.Widths)
  · have he : Geometry.b2583.half 2 false=Geometry.b2939 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2939
  · have he : Geometry.b2583.half 2 true=Geometry.b2940 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2940

theorem bound2582 : BoxMajorant Geometry.b2582 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2582.Widths)
  · have he : Geometry.b2582.half 2 false=Geometry.b2937 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2937
  · have he : Geometry.b2582.half 2 true=Geometry.b2938 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2938

theorem bound2581 : BoxMajorant Geometry.b2581 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2581 2 (by decide +kernel) x hx hd ho).elim

theorem bound2226 : BoxMajorant Geometry.b2226 := by
  exact PositiveLeaves.L1937.bound

theorem bound2225 : BoxMajorant Geometry.b2225 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2225.Widths)
  · have he : Geometry.b2225.half 1 false=Geometry.b2591 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2591
  · have he : Geometry.b2225.half 1 true=Geometry.b2592 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2592

theorem bound2224 : BoxMajorant Geometry.b2224 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2224.Widths)
  · have he : Geometry.b2224.half 1 false=Geometry.b2589 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2589
  · have he : Geometry.b2224.half 1 true=Geometry.b2590 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2590

theorem bound2223 : BoxMajorant Geometry.b2223 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2223 2 (by decide +kernel) x hx hd ho).elim

theorem bound2222 : BoxMajorant Geometry.b2222 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2222.Widths)
  · have he : Geometry.b2222.half 1 false=Geometry.b2587 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2587
  · have he : Geometry.b2222.half 1 true=Geometry.b2588 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2588

theorem bound2221 : BoxMajorant Geometry.b2221 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2221.Widths)
  · have he : Geometry.b2221.half 1 false=Geometry.b2585 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2585
  · have he : Geometry.b2221.half 1 true=Geometry.b2586 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2586

theorem bound2220 : BoxMajorant Geometry.b2220 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2220.Widths)
  · have he : Geometry.b2220.half 1 false=Geometry.b2583 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2583
  · have he : Geometry.b2220.half 1 true=Geometry.b2584 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2584

theorem bound2219 : BoxMajorant Geometry.b2219 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2219 2 (by decide +kernel) x hx hd ho).elim

theorem bound2218 : BoxMajorant Geometry.b2218 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2218.Widths)
  · have he : Geometry.b2218.half 1 false=Geometry.b2581 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2581
  · have he : Geometry.b2218.half 1 true=Geometry.b2582 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2582

theorem bound2217 : BoxMajorant Geometry.b2217 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2217 2 (by decide +kernel) x hx hd ho).elim

theorem bound1614 : BoxMajorant Geometry.b1614 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1614.Widths)
  · have he : Geometry.b1614.half 0 false=Geometry.b2225 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2225
  · have he : Geometry.b1614.half 0 true=Geometry.b2226 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2226

theorem bound1613 : BoxMajorant Geometry.b1613 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1613.Widths)
  · have he : Geometry.b1613.half 0 false=Geometry.b2223 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2223
  · have he : Geometry.b1613.half 0 true=Geometry.b2224 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2224

theorem bound1612 : BoxMajorant Geometry.b1612 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1612.Widths)
  · have he : Geometry.b1612.half 0 false=Geometry.b2221 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2221
  · have he : Geometry.b1612.half 0 true=Geometry.b2222 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2222

theorem bound1611 : BoxMajorant Geometry.b1611 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1611.Widths)
  · have he : Geometry.b1611.half 0 false=Geometry.b2219 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2219
  · have he : Geometry.b1611.half 0 true=Geometry.b2220 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2220

theorem bound1610 : BoxMajorant Geometry.b1610 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1610.Widths)
  · have he : Geometry.b1610.half 0 false=Geometry.b2217 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2217
  · have he : Geometry.b1610.half 0 true=Geometry.b2218 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2218

theorem bound1609 : BoxMajorant Geometry.b1609 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1609 2 (by decide +kernel) x hx hd ho).elim

theorem bound1144 : BoxMajorant Geometry.b1144 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1144.Widths)
  · have he : Geometry.b1144.half 2 false=Geometry.b1613 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1613
  · have he : Geometry.b1144.half 2 true=Geometry.b1614 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1614

theorem bound1143 : BoxMajorant Geometry.b1143 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1143.Widths)
  · have he : Geometry.b1143.half 2 false=Geometry.b1611 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1611
  · have he : Geometry.b1143.half 2 true=Geometry.b1612 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1612

theorem bound1142 : BoxMajorant Geometry.b1142 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1142.Widths)
  · have he : Geometry.b1142.half 2 false=Geometry.b1609 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1609
  · have he : Geometry.b1142.half 2 true=Geometry.b1610 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1610

theorem bound1141 : BoxMajorant Geometry.b1141 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1141 2 (by decide +kernel) x hx hd ho).elim

theorem bound830 : BoxMajorant Geometry.b830 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b830.Widths)
  · have he : Geometry.b830.half 1 false=Geometry.b1143 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1143
  · have he : Geometry.b830.half 1 true=Geometry.b1144 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1144

theorem bound829 : BoxMajorant Geometry.b829 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b829.Widths)
  · have he : Geometry.b829.half 1 false=Geometry.b1141 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1141
  · have he : Geometry.b829.half 1 true=Geometry.b1142 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1142

theorem bound554 : BoxMajorant Geometry.b554 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b554.Widths)
  · have he : Geometry.b554.half 0 false=Geometry.b829 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound829
  · have he : Geometry.b554.half 0 true=Geometry.b830 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound830

end N7.Kernel.Cover
