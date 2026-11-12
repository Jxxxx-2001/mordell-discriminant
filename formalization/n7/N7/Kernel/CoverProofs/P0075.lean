import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.PositiveGroups.G0043
import N7.Kernel.PositiveGroups.G0103
import N7.Kernel.PositiveGroups.G0104
import N7.Kernel.PositiveGroups.G0180
import N7.Kernel.PositiveGroups.G0222
import N7.Kernel.PositiveGroups.G0223
import N7.Kernel.PositiveGroups.G0224
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3384 : BoxMajorant Geometry.b3384 := by
  exact PositiveLeaves.L1421.bound

theorem bound3383 : BoxMajorant Geometry.b3383 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3383 2 (by decide +kernel) x hx hd ho).elim

theorem bound3382 : BoxMajorant Geometry.b3382 := by
  exact PositiveLeaves.L1426.bound

theorem bound3381 : BoxMajorant Geometry.b3381 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3381 2 (by decide +kernel) x hx hd ho).elim

theorem bound3380 : BoxMajorant Geometry.b3380 := by
  exact PositiveLeaves.L1429.bound

theorem bound3379 : BoxMajorant Geometry.b3379 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3379 2 (by decide +kernel) x hx hd ho).elim

theorem bound3042 : BoxMajorant Geometry.b3042 := by
  exact PositiveLeaves.L1420.bound

theorem bound3041 : BoxMajorant Geometry.b3041 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3041.Widths)
  · have he : Geometry.b3041.half 0 false=Geometry.b3383 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3383
  · have he : Geometry.b3041.half 0 true=Geometry.b3384 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3384

theorem bound3040 : BoxMajorant Geometry.b3040 := by
  exact PositiveLeaves.L1425.bound

theorem bound3039 : BoxMajorant Geometry.b3039 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3039.Widths)
  · have he : Geometry.b3039.half 0 false=Geometry.b3381 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3381
  · have he : Geometry.b3039.half 0 true=Geometry.b3382 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3382

theorem bound3038 : BoxMajorant Geometry.b3038 := by
  exact PositiveLeaves.L1428.bound

theorem bound3037 : BoxMajorant Geometry.b3037 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3037.Widths)
  · have he : Geometry.b3037.half 0 false=Geometry.b3379 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3379
  · have he : Geometry.b3037.half 0 true=Geometry.b3380 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3380

theorem bound2638 : BoxMajorant Geometry.b2638 := by
  exact PositiveLeaves.L1419.bound

theorem bound2637 : BoxMajorant Geometry.b2637 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2637.Widths)
  · have he : Geometry.b2637.half 2 false=Geometry.b3041 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3041
  · have he : Geometry.b2637.half 2 true=Geometry.b3042 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3042

theorem bound2636 : BoxMajorant Geometry.b2636 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2636.Widths)
  · have he : Geometry.b2636.half 2 false=Geometry.b3039 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3039
  · have he : Geometry.b2636.half 2 true=Geometry.b3040 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3040

theorem bound2635 : BoxMajorant Geometry.b2635 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2635.Widths)
  · have he : Geometry.b2635.half 2 false=Geometry.b3037 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3037
  · have he : Geometry.b2635.half 2 true=Geometry.b3038 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3038

theorem bound2264 : BoxMajorant Geometry.b2264 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2264.Widths)
  · have he : Geometry.b2264.half 1 false=Geometry.b2637 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2637
  · have he : Geometry.b2264.half 1 true=Geometry.b2638 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2638

theorem bound2263 : BoxMajorant Geometry.b2263 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2263 2 (by decide +kernel) x hx hd ho).elim

theorem bound2262 : BoxMajorant Geometry.b2262 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2262.Widths)
  · have he : Geometry.b2262.half 1 false=Geometry.b2635 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2635
  · have he : Geometry.b2262.half 1 true=Geometry.b2636 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2636

theorem bound2261 : BoxMajorant Geometry.b2261 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2261 2 (by decide +kernel) x hx hd ho).elim

theorem bound1646 : BoxMajorant Geometry.b1646 := by
  exact PositiveLeaves.L1418.bound

theorem bound1645 : BoxMajorant Geometry.b1645 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1645.Widths)
  · have he : Geometry.b1645.half 0 false=Geometry.b2263 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2263
  · have he : Geometry.b1645.half 0 true=Geometry.b2264 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2264

theorem bound1644 : BoxMajorant Geometry.b1644 := by
  exact PositiveLeaves.L1424.bound

theorem bound1643 : BoxMajorant Geometry.b1643 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1643.Widths)
  · have he : Geometry.b1643.half 0 false=Geometry.b2261 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2261
  · have he : Geometry.b1643.half 0 true=Geometry.b2262 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2262

theorem bound1160 : BoxMajorant Geometry.b1160 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1160.Widths)
  · have he : Geometry.b1160.half 2 false=Geometry.b1645 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1645
  · have he : Geometry.b1160.half 2 true=Geometry.b1646 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1646

theorem bound1159 : BoxMajorant Geometry.b1159 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1159.Widths)
  · have he : Geometry.b1159.half 2 false=Geometry.b1643 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1643
  · have he : Geometry.b1159.half 2 true=Geometry.b1644 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1644

theorem bound842 : BoxMajorant Geometry.b842 := by
  exact PositiveLeaves.L1417.bound

theorem bound841 : BoxMajorant Geometry.b841 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b841.Widths)
  · have he : Geometry.b841.half 1 false=Geometry.b1159 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1159
  · have he : Geometry.b841.half 1 true=Geometry.b1160 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1160

theorem bound561 : BoxMajorant Geometry.b561 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b561.Widths)
  · have he : Geometry.b561.half 0 false=Geometry.b841 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound841
  · have he : Geometry.b561.half 0 true=Geometry.b842 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound842

end N7.Kernel.Cover
