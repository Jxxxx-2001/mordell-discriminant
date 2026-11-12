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
import N7.Kernel.PositiveGroups.G0042
import N7.Kernel.PositiveGroups.G0068
import N7.Kernel.PositiveGroups.G0104
import N7.Kernel.PositiveGroups.G0181
import N7.Kernel.PositiveGroups.G0223
import N7.Kernel.PositiveGroups.G0224
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3378 : BoxMajorant Geometry.b3378 := by
  exact PositiveLeaves.L1436.bound

theorem bound3377 : BoxMajorant Geometry.b3377 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3377 2 (by decide +kernel) x hx hd ho).elim

theorem bound3376 : BoxMajorant Geometry.b3376 := by
  exact PositiveLeaves.L1439.bound

theorem bound3375 : BoxMajorant Geometry.b3375 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3375 2 (by decide +kernel) x hx hd ho).elim

theorem bound3036 : BoxMajorant Geometry.b3036 := by
  exact PositiveLeaves.L1435.bound

theorem bound3035 : BoxMajorant Geometry.b3035 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3035.Widths)
  · have he : Geometry.b3035.half 0 false=Geometry.b3377 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3377
  · have he : Geometry.b3035.half 0 true=Geometry.b3378 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3378

theorem bound3034 : BoxMajorant Geometry.b3034 := by
  exact PositiveLeaves.L1438.bound

theorem bound3033 : BoxMajorant Geometry.b3033 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3033.Widths)
  · have he : Geometry.b3033.half 0 false=Geometry.b3375 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3375
  · have he : Geometry.b3033.half 0 true=Geometry.b3376 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3376

theorem bound2634 : BoxMajorant Geometry.b2634 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2634.Widths)
  · have he : Geometry.b2634.half 2 false=Geometry.b3035 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3035
  · have he : Geometry.b2634.half 2 true=Geometry.b3036 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3036

theorem bound2633 : BoxMajorant Geometry.b2633 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2633.Widths)
  · have he : Geometry.b2633.half 2 false=Geometry.b3033 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3033
  · have he : Geometry.b2633.half 2 true=Geometry.b3034 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3034

theorem bound2260 : BoxMajorant Geometry.b2260 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2260.Widths)
  · have he : Geometry.b2260.half 1 false=Geometry.b2633 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2633
  · have he : Geometry.b2260.half 1 true=Geometry.b2634 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2634

theorem bound2259 : BoxMajorant Geometry.b2259 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2259 2 (by decide +kernel) x hx hd ho).elim

theorem bound2258 : BoxMajorant Geometry.b2258 := by
  exact PositiveLeaves.L1443.bound

theorem bound2257 : BoxMajorant Geometry.b2257 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2257 2 (by decide +kernel) x hx hd ho).elim

theorem bound1642 : BoxMajorant Geometry.b1642 := by
  exact PositiveLeaves.L1434.bound

theorem bound1641 : BoxMajorant Geometry.b1641 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1641.Widths)
  · have he : Geometry.b1641.half 0 false=Geometry.b2259 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2259
  · have he : Geometry.b1641.half 0 true=Geometry.b2260 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2260

theorem bound1640 : BoxMajorant Geometry.b1640 := by
  exact PositiveLeaves.L1442.bound

theorem bound1639 : BoxMajorant Geometry.b1639 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1639.Widths)
  · have he : Geometry.b1639.half 0 false=Geometry.b2257 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2257
  · have he : Geometry.b1639.half 0 true=Geometry.b2258 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2258

theorem bound1158 : BoxMajorant Geometry.b1158 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1158.Widths)
  · have he : Geometry.b1158.half 2 false=Geometry.b1641 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1641
  · have he : Geometry.b1158.half 2 true=Geometry.b1642 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1642

theorem bound1157 : BoxMajorant Geometry.b1157 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1157.Widths)
  · have he : Geometry.b1157.half 2 false=Geometry.b1639 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1639
  · have he : Geometry.b1157.half 2 true=Geometry.b1640 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1640

theorem bound840 : BoxMajorant Geometry.b840 := by
  exact PositiveLeaves.L1433.bound

theorem bound839 : BoxMajorant Geometry.b839 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b839.Widths)
  · have he : Geometry.b839.half 1 false=Geometry.b1157 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1157
  · have he : Geometry.b839.half 1 true=Geometry.b1158 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1158

theorem bound559 : BoxMajorant Geometry.b559 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b559.Widths)
  · have he : Geometry.b559.half 0 false=Geometry.b839 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound839
  · have he : Geometry.b559.half 0 true=Geometry.b840 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound840

end N7.Kernel.Cover
