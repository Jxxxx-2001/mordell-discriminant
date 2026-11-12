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
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverProofs.P0273
import N7.Kernel.CoverProofs.P0274
import N7.Kernel.CoverProofs.P0275
import N7.Kernel.CoverProofs.P0276
import N7.Kernel.CoverProofs.P0277
import N7.Kernel.CoverProofs.P0278
import N7.Kernel.CoverProofs.P0279
import N7.Kernel.CoverProofs.P0280
import N7.Kernel.CoverProofs.P0281
import N7.Kernel.CoverProofs.P0282
import N7.Kernel.PositiveGroups.G0043
import N7.Kernel.PositiveGroups.G0144
import N7.Kernel.PositiveGroups.G0145
import N7.Kernel.PositiveGroups.G0181
import N7.Kernel.PositiveGroups.G0224
import N7.Kernel.PositiveGroups.G0225
import N7.Kernel.PositiveGroups.G0260
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4031 : BoxMajorant Geometry.b4031 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4031 2 (by decide +kernel) x hx hd ho).elim

theorem bound4029 : BoxMajorant Geometry.b4029 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4029 2 (by decide +kernel) x hx hd ho).elim

theorem bound3646 : BoxMajorant Geometry.b3646 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3646.Widths)
  · have he : Geometry.b3646.half 2 false=Geometry.b4031 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4031
  · have he : Geometry.b3646.half 2 true=Geometry.b4032 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4032

theorem bound3645 : BoxMajorant Geometry.b3645 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3645.Widths)
  · have he : Geometry.b3645.half 2 false=Geometry.b4029 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4029
  · have he : Geometry.b3645.half 2 true=Geometry.b4030 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4030

theorem bound3374 : BoxMajorant Geometry.b3374 := by
  exact PositiveLeaves.L1450.bound

theorem bound3373 : BoxMajorant Geometry.b3373 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3373.Widths)
  · have he : Geometry.b3373.half 1 false=Geometry.b3653 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3653
  · have he : Geometry.b3373.half 1 true=Geometry.b3654 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3654

theorem bound3372 : BoxMajorant Geometry.b3372 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3372.Widths)
  · have he : Geometry.b3372.half 1 false=Geometry.b3651 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3651
  · have he : Geometry.b3372.half 1 true=Geometry.b3652 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3652

theorem bound3371 : BoxMajorant Geometry.b3371 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3371.Widths)
  · have he : Geometry.b3371.half 1 false=Geometry.b3649 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3649
  · have he : Geometry.b3371.half 1 true=Geometry.b3650 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3650

theorem bound3370 : BoxMajorant Geometry.b3370 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3370.Widths)
  · have he : Geometry.b3370.half 1 false=Geometry.b3647 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3647
  · have he : Geometry.b3370.half 1 true=Geometry.b3648 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3648

theorem bound3369 : BoxMajorant Geometry.b3369 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3369.Widths)
  · have he : Geometry.b3369.half 1 false=Geometry.b3645 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3645
  · have he : Geometry.b3369.half 1 true=Geometry.b3646 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3646

theorem bound3032 : BoxMajorant Geometry.b3032 := by
  exact PositiveLeaves.L1449.bound

theorem bound3031 : BoxMajorant Geometry.b3031 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3031.Widths)
  · have he : Geometry.b3031.half 0 false=Geometry.b3373 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3373
  · have he : Geometry.b3031.half 0 true=Geometry.b3374 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3374

theorem bound3030 : BoxMajorant Geometry.b3030 := by
  exact PositiveLeaves.L1461.bound

theorem bound3029 : BoxMajorant Geometry.b3029 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3029.Widths)
  · have he : Geometry.b3029.half 0 false=Geometry.b3371 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3371
  · have he : Geometry.b3029.half 0 true=Geometry.b3372 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3372

theorem bound3028 : BoxMajorant Geometry.b3028 := by
  exact PositiveLeaves.L1502.bound

theorem bound3027 : BoxMajorant Geometry.b3027 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3027.Widths)
  · have he : Geometry.b3027.half 0 false=Geometry.b3369 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3369
  · have he : Geometry.b3027.half 0 true=Geometry.b3370 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3370

theorem bound2632 : BoxMajorant Geometry.b2632 := by
  exact PositiveLeaves.L1448.bound

theorem bound2631 : BoxMajorant Geometry.b2631 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2631.Widths)
  · have he : Geometry.b2631.half 2 false=Geometry.b3031 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3031
  · have he : Geometry.b2631.half 2 true=Geometry.b3032 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3032

theorem bound2630 : BoxMajorant Geometry.b2630 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2630.Widths)
  · have he : Geometry.b2630.half 2 false=Geometry.b3029 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3029
  · have he : Geometry.b2630.half 2 true=Geometry.b3030 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3030

theorem bound2629 : BoxMajorant Geometry.b2629 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2629.Widths)
  · have he : Geometry.b2629.half 2 false=Geometry.b3027 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3027
  · have he : Geometry.b2629.half 2 true=Geometry.b3028 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3028

theorem bound2256 : BoxMajorant Geometry.b2256 := by
  exact PositiveLeaves.L1447.bound

theorem bound2255 : BoxMajorant Geometry.b2255 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2255.Widths)
  · have he : Geometry.b2255.half 1 false=Geometry.b2631 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2631
  · have he : Geometry.b2255.half 1 true=Geometry.b2632 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2632

theorem bound2254 : BoxMajorant Geometry.b2254 := by
  exact PositiveLeaves.L1460.bound

theorem bound2253 : BoxMajorant Geometry.b2253 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2253.Widths)
  · have he : Geometry.b2253.half 1 false=Geometry.b2629 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2629
  · have he : Geometry.b2253.half 1 true=Geometry.b2630 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2630

theorem bound1638 : BoxMajorant Geometry.b1638 := by
  exact PositiveLeaves.L1446.bound

theorem bound1637 : BoxMajorant Geometry.b1637 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1637.Widths)
  · have he : Geometry.b1637.half 0 false=Geometry.b2255 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2255
  · have he : Geometry.b1637.half 0 true=Geometry.b2256 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2256

theorem bound1636 : BoxMajorant Geometry.b1636 := by
  exact PositiveLeaves.L1459.bound

theorem bound1635 : BoxMajorant Geometry.b1635 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1635.Widths)
  · have he : Geometry.b1635.half 0 false=Geometry.b2253 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2253
  · have he : Geometry.b1635.half 0 true=Geometry.b2254 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2254

theorem bound1156 : BoxMajorant Geometry.b1156 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1156.Widths)
  · have he : Geometry.b1156.half 2 false=Geometry.b1637 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1637
  · have he : Geometry.b1156.half 2 true=Geometry.b1638 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1638

theorem bound1155 : BoxMajorant Geometry.b1155 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1155.Widths)
  · have he : Geometry.b1155.half 2 false=Geometry.b1635 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1635
  · have he : Geometry.b1155.half 2 true=Geometry.b1636 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1636

theorem bound838 : BoxMajorant Geometry.b838 := by
  exact PositiveLeaves.L1445.bound

theorem bound837 : BoxMajorant Geometry.b837 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b837.Widths)
  · have he : Geometry.b837.half 1 false=Geometry.b1155 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1155
  · have he : Geometry.b837.half 1 true=Geometry.b1156 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1156

theorem bound558 : BoxMajorant Geometry.b558 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b558.Widths)
  · have he : Geometry.b558.half 0 false=Geometry.b837 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound837
  · have he : Geometry.b558.half 0 true=Geometry.b838 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound838

end N7.Kernel.Cover
