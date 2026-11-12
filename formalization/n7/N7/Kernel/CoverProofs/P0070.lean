import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverProofs.P0236
import N7.Kernel.CoverProofs.P0237
import N7.Kernel.CoverProofs.P0238
import N7.Kernel.CoverProofs.P0239
import N7.Kernel.CoverProofs.P0240
import N7.Kernel.CoverProofs.P0241
import N7.Kernel.CoverProofs.P0242
import N7.Kernel.CoverProofs.P0243
import N7.Kernel.CoverProofs.P0244
import N7.Kernel.CoverProofs.P0245
import N7.Kernel.CoverProofs.P0246
import N7.Kernel.CoverProofs.P0247
import N7.Kernel.CoverProofs.P0248
import N7.Kernel.PositiveGroups.G0182
import N7.Kernel.PositiveGroups.G0225
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2965 : BoxMajorant Geometry.b2965 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2965 2 (by decide +kernel) x hx hd ho).elim

theorem bound2963 : BoxMajorant Geometry.b2963 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2963 2 (by decide +kernel) x hx hd ho).elim

theorem bound2961 : BoxMajorant Geometry.b2961 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2961 2 (by decide +kernel) x hx hd ho).elim

theorem bound2959 : BoxMajorant Geometry.b2959 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2959 2 (by decide +kernel) x hx hd ho).elim

theorem bound2601 : BoxMajorant Geometry.b2601 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2601 2 (by decide +kernel) x hx hd ho).elim

theorem bound2596 : BoxMajorant Geometry.b2596 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2596.Widths)
  · have he : Geometry.b2596.half 2 false=Geometry.b2965 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2965
  · have he : Geometry.b2596.half 2 true=Geometry.b2966 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2966

theorem bound2595 : BoxMajorant Geometry.b2595 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2595.Widths)
  · have he : Geometry.b2595.half 2 false=Geometry.b2963 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2963
  · have he : Geometry.b2595.half 2 true=Geometry.b2964 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2964

theorem bound2594 : BoxMajorant Geometry.b2594 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2594.Widths)
  · have he : Geometry.b2594.half 2 false=Geometry.b2961 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2961
  · have he : Geometry.b2594.half 2 true=Geometry.b2962 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2962

theorem bound2593 : BoxMajorant Geometry.b2593 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2593.Widths)
  · have he : Geometry.b2593.half 2 false=Geometry.b2959 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2959
  · have he : Geometry.b2593.half 2 true=Geometry.b2960 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2960

theorem bound2238 : BoxMajorant Geometry.b2238 := by
  exact PositiveLeaves.L1831.bound

theorem bound2237 : BoxMajorant Geometry.b2237 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2237.Widths)
  · have he : Geometry.b2237.half 1 false=Geometry.b2605 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2605
  · have he : Geometry.b2237.half 1 true=Geometry.b2606 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2606

theorem bound2236 : BoxMajorant Geometry.b2236 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2236.Widths)
  · have he : Geometry.b2236.half 1 false=Geometry.b2603 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2603
  · have he : Geometry.b2236.half 1 true=Geometry.b2604 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2604

theorem bound2235 : BoxMajorant Geometry.b2235 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2235.Widths)
  · have he : Geometry.b2235.half 1 false=Geometry.b2601 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2601
  · have he : Geometry.b2235.half 1 true=Geometry.b2602 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2602

theorem bound2234 : BoxMajorant Geometry.b2234 := by
  exact PositiveLeaves.L1874.bound

theorem bound2233 : BoxMajorant Geometry.b2233 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2233.Widths)
  · have he : Geometry.b2233.half 1 false=Geometry.b2599 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2599
  · have he : Geometry.b2233.half 1 true=Geometry.b2600 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2600

theorem bound2232 : BoxMajorant Geometry.b2232 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2232.Widths)
  · have he : Geometry.b2232.half 1 false=Geometry.b2597 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2597
  · have he : Geometry.b2232.half 1 true=Geometry.b2598 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2598

theorem bound2231 : BoxMajorant Geometry.b2231 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2231 2 (by decide +kernel) x hx hd ho).elim

theorem bound2230 : BoxMajorant Geometry.b2230 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2230.Widths)
  · have he : Geometry.b2230.half 1 false=Geometry.b2595 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2595
  · have he : Geometry.b2230.half 1 true=Geometry.b2596 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2596

theorem bound2229 : BoxMajorant Geometry.b2229 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2229 2 (by decide +kernel) x hx hd ho).elim

theorem bound2228 : BoxMajorant Geometry.b2228 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2228.Widths)
  · have he : Geometry.b2228.half 1 false=Geometry.b2593 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2593
  · have he : Geometry.b2228.half 1 true=Geometry.b2594 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2594

theorem bound2227 : BoxMajorant Geometry.b2227 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2227 2 (by decide +kernel) x hx hd ho).elim

theorem bound1622 : BoxMajorant Geometry.b1622 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1622.Widths)
  · have he : Geometry.b1622.half 0 false=Geometry.b2237 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2237
  · have he : Geometry.b1622.half 0 true=Geometry.b2238 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2238

theorem bound1621 : BoxMajorant Geometry.b1621 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1621.Widths)
  · have he : Geometry.b1621.half 0 false=Geometry.b2235 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2235
  · have he : Geometry.b1621.half 0 true=Geometry.b2236 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2236

theorem bound1620 : BoxMajorant Geometry.b1620 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1620.Widths)
  · have he : Geometry.b1620.half 0 false=Geometry.b2233 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2233
  · have he : Geometry.b1620.half 0 true=Geometry.b2234 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2234

theorem bound1619 : BoxMajorant Geometry.b1619 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1619.Widths)
  · have he : Geometry.b1619.half 0 false=Geometry.b2231 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2231
  · have he : Geometry.b1619.half 0 true=Geometry.b2232 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2232

theorem bound1618 : BoxMajorant Geometry.b1618 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1618.Widths)
  · have he : Geometry.b1618.half 0 false=Geometry.b2229 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2229
  · have he : Geometry.b1618.half 0 true=Geometry.b2230 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2230

theorem bound1617 : BoxMajorant Geometry.b1617 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1617 2 (by decide +kernel) x hx hd ho).elim

theorem bound1616 : BoxMajorant Geometry.b1616 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1616.Widths)
  · have he : Geometry.b1616.half 0 false=Geometry.b2227 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2227
  · have he : Geometry.b1616.half 0 true=Geometry.b2228 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2228

theorem bound1615 : BoxMajorant Geometry.b1615 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1615 2 (by decide +kernel) x hx hd ho).elim

theorem bound1148 : BoxMajorant Geometry.b1148 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1148.Widths)
  · have he : Geometry.b1148.half 2 false=Geometry.b1621 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1621
  · have he : Geometry.b1148.half 2 true=Geometry.b1622 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1622

theorem bound1147 : BoxMajorant Geometry.b1147 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1147.Widths)
  · have he : Geometry.b1147.half 2 false=Geometry.b1619 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1619
  · have he : Geometry.b1147.half 2 true=Geometry.b1620 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1620

theorem bound1146 : BoxMajorant Geometry.b1146 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1146.Widths)
  · have he : Geometry.b1146.half 2 false=Geometry.b1617 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1617
  · have he : Geometry.b1146.half 2 true=Geometry.b1618 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1618

theorem bound1145 : BoxMajorant Geometry.b1145 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1145.Widths)
  · have he : Geometry.b1145.half 2 false=Geometry.b1615 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1615
  · have he : Geometry.b1145.half 2 true=Geometry.b1616 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1616

theorem bound832 : BoxMajorant Geometry.b832 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b832.Widths)
  · have he : Geometry.b832.half 1 false=Geometry.b1147 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1147
  · have he : Geometry.b832.half 1 true=Geometry.b1148 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1148

theorem bound831 : BoxMajorant Geometry.b831 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b831.Widths)
  · have he : Geometry.b831.half 1 false=Geometry.b1145 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1145
  · have he : Geometry.b831.half 1 true=Geometry.b1146 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1146

theorem bound555 : BoxMajorant Geometry.b555 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b555.Widths)
  · have he : Geometry.b555.half 0 false=Geometry.b831 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound831
  · have he : Geometry.b555.half 0 true=Geometry.b832 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound832

end N7.Kernel.Cover
