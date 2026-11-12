import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverProofs.P0254
import N7.Kernel.CoverProofs.P0255
import N7.Kernel.CoverProofs.P0256
import N7.Kernel.CoverProofs.P0257
import N7.Kernel.CoverProofs.P0258
import N7.Kernel.CoverProofs.P0259
import N7.Kernel.CoverProofs.P0260
import N7.Kernel.CoverProofs.P0261
import N7.Kernel.CoverProofs.P0262
import N7.Kernel.CoverProofs.P0263
import N7.Kernel.CoverProofs.P0264
import N7.Kernel.CoverProofs.P0265
import N7.Kernel.CoverProofs.P0266
import N7.Kernel.CoverProofs.P0267
import N7.Kernel.CoverProofs.P0268
import N7.Kernel.CoverProofs.P0269
import N7.Kernel.CoverProofs.P0270
import N7.Kernel.CoverProofs.P0271
import N7.Kernel.CoverProofs.P0272
import N7.Kernel.PositiveGroups.G0104
import N7.Kernel.PositiveGroups.G0182
import N7.Kernel.PositiveGroups.G0225
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3003 : BoxMajorant Geometry.b3003 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3003 2 (by decide +kernel) x hx hd ho).elim

theorem bound3001 : BoxMajorant Geometry.b3001 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3001 2 (by decide +kernel) x hx hd ho).elim

theorem bound2995 : BoxMajorant Geometry.b2995 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2995 2 (by decide +kernel) x hx hd ho).elim

theorem bound2993 : BoxMajorant Geometry.b2993 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2993 2 (by decide +kernel) x hx hd ho).elim

theorem bound2628 : BoxMajorant Geometry.b2628 := by
  exact PositiveLeaves.L1547.bound

theorem bound2616 : BoxMajorant Geometry.b2616 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2616.Widths)
  · have he : Geometry.b2616.half 2 false=Geometry.b3003 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3003
  · have he : Geometry.b2616.half 2 true=Geometry.b3004 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3004

theorem bound2615 : BoxMajorant Geometry.b2615 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2615.Widths)
  · have he : Geometry.b2615.half 2 false=Geometry.b3001 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3001
  · have he : Geometry.b2615.half 2 true=Geometry.b3002 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3002

theorem bound2614 : BoxMajorant Geometry.b2614 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2614.Widths)
  · have he : Geometry.b2614.half 2 false=Geometry.b2999 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2999
  · have he : Geometry.b2614.half 2 true=Geometry.b3000 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3000

theorem bound2613 : BoxMajorant Geometry.b2613 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2613.Widths)
  · have he : Geometry.b2613.half 2 false=Geometry.b2997 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2997
  · have he : Geometry.b2613.half 2 true=Geometry.b2998 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2998

theorem bound2612 : BoxMajorant Geometry.b2612 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2612.Widths)
  · have he : Geometry.b2612.half 2 false=Geometry.b2995 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2995
  · have he : Geometry.b2612.half 2 true=Geometry.b2996 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2996

theorem bound2611 : BoxMajorant Geometry.b2611 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2611.Widths)
  · have he : Geometry.b2611.half 2 false=Geometry.b2993 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2993
  · have he : Geometry.b2611.half 2 true=Geometry.b2994 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2994

theorem bound2252 : BoxMajorant Geometry.b2252 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2252.Widths)
  · have he : Geometry.b2252.half 1 false=Geometry.b2627 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2627
  · have he : Geometry.b2252.half 1 true=Geometry.b2628 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2628

theorem bound2251 : BoxMajorant Geometry.b2251 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2251.Widths)
  · have he : Geometry.b2251.half 1 false=Geometry.b2625 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2625
  · have he : Geometry.b2251.half 1 true=Geometry.b2626 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2626

theorem bound2250 : BoxMajorant Geometry.b2250 := by
  exact PositiveLeaves.L1562.bound

theorem bound2249 : BoxMajorant Geometry.b2249 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2249.Widths)
  · have he : Geometry.b2249.half 1 false=Geometry.b2623 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2623
  · have he : Geometry.b2249.half 1 true=Geometry.b2624 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2624

theorem bound2248 : BoxMajorant Geometry.b2248 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2248.Widths)
  · have he : Geometry.b2248.half 1 false=Geometry.b2621 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2621
  · have he : Geometry.b2248.half 1 true=Geometry.b2622 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2622

theorem bound2247 : BoxMajorant Geometry.b2247 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2247.Widths)
  · have he : Geometry.b2247.half 1 false=Geometry.b2619 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2619
  · have he : Geometry.b2247.half 1 true=Geometry.b2620 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2620

theorem bound2246 : BoxMajorant Geometry.b2246 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2246.Widths)
  · have he : Geometry.b2246.half 1 false=Geometry.b2617 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2617
  · have he : Geometry.b2246.half 1 true=Geometry.b2618 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2618

theorem bound2245 : BoxMajorant Geometry.b2245 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2245.Widths)
  · have he : Geometry.b2245.half 1 false=Geometry.b2615 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2615
  · have he : Geometry.b2245.half 1 true=Geometry.b2616 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2616

theorem bound2244 : BoxMajorant Geometry.b2244 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2244.Widths)
  · have he : Geometry.b2244.half 1 false=Geometry.b2613 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2613
  · have he : Geometry.b2244.half 1 true=Geometry.b2614 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2614

theorem bound2243 : BoxMajorant Geometry.b2243 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2243.Widths)
  · have he : Geometry.b2243.half 1 false=Geometry.b2611 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2611
  · have he : Geometry.b2243.half 1 true=Geometry.b2612 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2612

theorem bound1634 : BoxMajorant Geometry.b1634 := by
  exact PositiveLeaves.L1546.bound

theorem bound1633 : BoxMajorant Geometry.b1633 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1633.Widths)
  · have he : Geometry.b1633.half 0 false=Geometry.b2251 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2251
  · have he : Geometry.b1633.half 0 true=Geometry.b2252 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2252

theorem bound1632 : BoxMajorant Geometry.b1632 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1632.Widths)
  · have he : Geometry.b1632.half 0 false=Geometry.b2249 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2249
  · have he : Geometry.b1632.half 0 true=Geometry.b2250 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2250

theorem bound1631 : BoxMajorant Geometry.b1631 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1631.Widths)
  · have he : Geometry.b1631.half 0 false=Geometry.b2247 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2247
  · have he : Geometry.b1631.half 0 true=Geometry.b2248 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2248

theorem bound1630 : BoxMajorant Geometry.b1630 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1630.Widths)
  · have he : Geometry.b1630.half 0 false=Geometry.b2245 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2245
  · have he : Geometry.b1630.half 0 true=Geometry.b2246 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2246

theorem bound1629 : BoxMajorant Geometry.b1629 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1629 2 (by decide +kernel) x hx hd ho).elim

theorem bound1628 : BoxMajorant Geometry.b1628 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1628.Widths)
  · have he : Geometry.b1628.half 0 false=Geometry.b2243 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2243
  · have he : Geometry.b1628.half 0 true=Geometry.b2244 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2244

theorem bound1627 : BoxMajorant Geometry.b1627 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1627 2 (by decide +kernel) x hx hd ho).elim

theorem bound1154 : BoxMajorant Geometry.b1154 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1154.Widths)
  · have he : Geometry.b1154.half 2 false=Geometry.b1633 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1633
  · have he : Geometry.b1154.half 2 true=Geometry.b1634 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1634

theorem bound1153 : BoxMajorant Geometry.b1153 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1153.Widths)
  · have he : Geometry.b1153.half 2 false=Geometry.b1631 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1631
  · have he : Geometry.b1153.half 2 true=Geometry.b1632 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1632

theorem bound1152 : BoxMajorant Geometry.b1152 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1152.Widths)
  · have he : Geometry.b1152.half 2 false=Geometry.b1629 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1629
  · have he : Geometry.b1152.half 2 true=Geometry.b1630 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1630

theorem bound1151 : BoxMajorant Geometry.b1151 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1151.Widths)
  · have he : Geometry.b1151.half 2 false=Geometry.b1627 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1627
  · have he : Geometry.b1151.half 2 true=Geometry.b1628 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1628

theorem bound836 : BoxMajorant Geometry.b836 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b836.Widths)
  · have he : Geometry.b836.half 1 false=Geometry.b1153 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1153
  · have he : Geometry.b836.half 1 true=Geometry.b1154 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1154

theorem bound835 : BoxMajorant Geometry.b835 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b835.Widths)
  · have he : Geometry.b835.half 1 false=Geometry.b1151 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1151
  · have he : Geometry.b835.half 1 true=Geometry.b1152 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1152

theorem bound557 : BoxMajorant Geometry.b557 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b557.Widths)
  · have he : Geometry.b557.half 0 false=Geometry.b835 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound835
  · have he : Geometry.b557.half 0 true=Geometry.b836 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound836

end N7.Kernel.Cover
