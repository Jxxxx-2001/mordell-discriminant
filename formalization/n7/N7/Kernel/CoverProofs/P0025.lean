import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0004
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverProofs.P0184
import N7.Kernel.CoverProofs.P0185
import N7.Kernel.PositiveGroups.G0004
import N7.Kernel.PositiveGroups.G0008
import N7.Kernel.PositiveGroups.G0015
import N7.Kernel.PositiveGroups.G0016
import N7.Kernel.PositiveGroups.G0033
import N7.Kernel.PositiveGroups.G0060
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1028 : BoxMajorant Geometry.b1028 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1028 0 (by decide +kernel) x hx hd ho).elim

theorem bound1027 : BoxMajorant Geometry.b1027 := by
  exact PositiveLeaves.L4.bound

theorem bound1025 : BoxMajorant Geometry.b1025 := by
  exact PositiveLeaves.L8.bound

theorem bound1024 : BoxMajorant Geometry.b1024 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1024 0 (by decide +kernel) x hx hd ho).elim

theorem bound746 : BoxMajorant Geometry.b746 := by
  exact PositiveLeaves.L0.bound

theorem bound745 : BoxMajorant Geometry.b745 := by
  exact PositiveLeaves.L1.bound

theorem bound744 : BoxMajorant Geometry.b744 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b744 1 (by decide +kernel) x hx hd ho).elim

theorem bound743 : BoxMajorant Geometry.b743 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b743.Widths)
  · have he : Geometry.b743.half 0 false=Geometry.b1027 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1027
  · have he : Geometry.b743.half 0 true=Geometry.b1028 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1028

theorem bound742 : BoxMajorant Geometry.b742 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b742 1 (by decide +kernel) x hx hd ho).elim

theorem bound741 : BoxMajorant Geometry.b741 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b741.Widths)
  · have he : Geometry.b741.half 0 false=Geometry.b1025 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1025
  · have he : Geometry.b741.half 0 true=Geometry.b1026 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1026

theorem bound740 : BoxMajorant Geometry.b740 := by
  exact PositiveLeaves.L12.bound

theorem bound739 : BoxMajorant Geometry.b739 := by
  exact PositiveLeaves.L13.bound

theorem bound738 : BoxMajorant Geometry.b738 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b738.Widths)
  · have he : Geometry.b738.half 0 false=Geometry.b1023 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1023
  · have he : Geometry.b738.half 0 true=Geometry.b1024 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1024

theorem bound737 : BoxMajorant Geometry.b737 := by
  exact PositiveLeaves.L20.bound

theorem bound478 : BoxMajorant Geometry.b478 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b478.Widths)
  · have he : Geometry.b478.half 2 false=Geometry.b745 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound745
  · have he : Geometry.b478.half 2 true=Geometry.b746 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound746

theorem bound477 : BoxMajorant Geometry.b477 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b477.Widths)
  · have he : Geometry.b477.half 2 false=Geometry.b743 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound743
  · have he : Geometry.b477.half 2 true=Geometry.b744 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound744

theorem bound476 : BoxMajorant Geometry.b476 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b476.Widths)
  · have he : Geometry.b476.half 2 false=Geometry.b741 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound741
  · have he : Geometry.b476.half 2 true=Geometry.b742 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound742

theorem bound475 : BoxMajorant Geometry.b475 := by
  exact PositiveLeaves.L9.bound

theorem bound474 : BoxMajorant Geometry.b474 := by
  exact PositiveLeaves.L11.bound

theorem bound473 : BoxMajorant Geometry.b473 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b473.Widths)
  · have he : Geometry.b473.half 2 false=Geometry.b739 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound739
  · have he : Geometry.b473.half 2 true=Geometry.b740 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound740

theorem bound472 : BoxMajorant Geometry.b472 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b472.Widths)
  · have he : Geometry.b472.half 2 false=Geometry.b737 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound737
  · have he : Geometry.b472.half 2 true=Geometry.b738 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound738

theorem bound471 : BoxMajorant Geometry.b471 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b471 0 (by decide +kernel) x hx hd ho).elim

theorem bound304 : BoxMajorant Geometry.b304 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b304.Widths)
  · have he : Geometry.b304.half 1 false=Geometry.b477 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound477
  · have he : Geometry.b304.half 1 true=Geometry.b478 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound478

theorem bound303 : BoxMajorant Geometry.b303 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b303.Widths)
  · have he : Geometry.b303.half 1 false=Geometry.b475 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound475
  · have he : Geometry.b303.half 1 true=Geometry.b476 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound476

theorem bound302 : BoxMajorant Geometry.b302 := by
  exact PositiveLeaves.L10.bound

theorem bound301 : BoxMajorant Geometry.b301 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b301.Widths)
  · have he : Geometry.b301.half 1 false=Geometry.b473 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound473
  · have he : Geometry.b301.half 1 true=Geometry.b474 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound474

theorem bound300 : BoxMajorant Geometry.b300 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b300 0 (by decide +kernel) x hx hd ho).elim

theorem bound299 : BoxMajorant Geometry.b299 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b299.Widths)
  · have he : Geometry.b299.half 1 false=Geometry.b471 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound471
  · have he : Geometry.b299.half 1 true=Geometry.b472 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound472

theorem bound190 : BoxMajorant Geometry.b190 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b190.Widths)
  · have he : Geometry.b190.half 0 false=Geometry.b303 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound303
  · have he : Geometry.b190.half 0 true=Geometry.b304 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound304

theorem bound189 : BoxMajorant Geometry.b189 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b189.Widths)
  · have he : Geometry.b189.half 0 false=Geometry.b301 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound301
  · have he : Geometry.b189.half 0 true=Geometry.b302 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound302

theorem bound188 : BoxMajorant Geometry.b188 := by
  exact PositiveLeaves.L14.bound

theorem bound187 : BoxMajorant Geometry.b187 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b187.Widths)
  · have he : Geometry.b187.half 0 false=Geometry.b299 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound299
  · have he : Geometry.b187.half 0 true=Geometry.b300 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound300

theorem bound110 : BoxMajorant Geometry.b110 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b110.Widths)
  · have he : Geometry.b110.half 2 false=Geometry.b189 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound189
  · have he : Geometry.b110.half 2 true=Geometry.b190 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound190

theorem bound109 : BoxMajorant Geometry.b109 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b109.Widths)
  · have he : Geometry.b109.half 2 false=Geometry.b187 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound187
  · have he : Geometry.b109.half 2 true=Geometry.b188 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound188

theorem bound60 : BoxMajorant Geometry.b60 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b60.Widths)
  · have he : Geometry.b60.half 1 false=Geometry.b109 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound109
  · have he : Geometry.b60.half 1 true=Geometry.b110 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound110

end N7.Kernel.Cover
