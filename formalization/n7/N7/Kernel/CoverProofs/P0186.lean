import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverProofs.P0333
import N7.Kernel.CoverProofs.P0334
import N7.Kernel.CoverProofs.P0335
import N7.Kernel.PositiveGroups.G0386
import N7.Kernel.PositiveGroups.G0409
import N7.Kernel.PositiveGroups.G0410
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5110 : BoxMajorant Geometry.b5110 := by
  exact PositiveLeaves.L2881.bound

theorem bound5108 : BoxMajorant Geometry.b5108 := by
  exact PositiveLeaves.L2886.bound

theorem bound5107 : BoxMajorant Geometry.b5107 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5107 2 (by decide +kernel) x hx hd ho).elim

theorem bound5106 : BoxMajorant Geometry.b5106 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5106.Widths)
  · have he : Geometry.b5106.half 1 false=Geometry.b5283 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5283
  · have he : Geometry.b5106.half 1 true=Geometry.b5284 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5284

theorem bound5105 : BoxMajorant Geometry.b5105 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5105 2 (by decide +kernel) x hx hd ho).elim

theorem bound4728 : BoxMajorant Geometry.b4728 := by
  exact PositiveLeaves.L2879.bound

theorem bound4727 : BoxMajorant Geometry.b4727 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4727 2 (by decide +kernel) x hx hd ho).elim

theorem bound4726 : BoxMajorant Geometry.b4726 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4726.Widths)
  · have he : Geometry.b4726.half 0 false=Geometry.b5109 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5109
  · have he : Geometry.b4726.half 0 true=Geometry.b5110 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5110

theorem bound4725 : BoxMajorant Geometry.b4725 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4725 2 (by decide +kernel) x hx hd ho).elim

theorem bound4724 : BoxMajorant Geometry.b4724 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4724.Widths)
  · have he : Geometry.b4724.half 0 false=Geometry.b5107 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5107
  · have he : Geometry.b4724.half 0 true=Geometry.b5108 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5108

theorem bound4723 : BoxMajorant Geometry.b4723 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4723 2 (by decide +kernel) x hx hd ho).elim

theorem bound4722 : BoxMajorant Geometry.b4722 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4722.Widths)
  · have he : Geometry.b4722.half 0 false=Geometry.b5105 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5105
  · have he : Geometry.b4722.half 0 true=Geometry.b5106 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5106

theorem bound4721 : BoxMajorant Geometry.b4721 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4721 2 (by decide +kernel) x hx hd ho).elim

theorem bound4450 : BoxMajorant Geometry.b4450 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4450.Widths)
  · have he : Geometry.b4450.half 2 false=Geometry.b4727 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4727
  · have he : Geometry.b4450.half 2 true=Geometry.b4728 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4728

theorem bound4449 : BoxMajorant Geometry.b4449 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4449.Widths)
  · have he : Geometry.b4449.half 2 false=Geometry.b4725 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4725
  · have he : Geometry.b4449.half 2 true=Geometry.b4726 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4726

theorem bound4448 : BoxMajorant Geometry.b4448 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4448.Widths)
  · have he : Geometry.b4448.half 2 false=Geometry.b4723 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4723
  · have he : Geometry.b4448.half 2 true=Geometry.b4724 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4724

theorem bound4447 : BoxMajorant Geometry.b4447 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4447 2 (by decide +kernel) x hx hd ho).elim

theorem bound4446 : BoxMajorant Geometry.b4446 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4446.Widths)
  · have he : Geometry.b4446.half 2 false=Geometry.b4721 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4721
  · have he : Geometry.b4446.half 2 true=Geometry.b4722 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4722

theorem bound4445 : BoxMajorant Geometry.b4445 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4445 2 (by decide +kernel) x hx hd ho).elim

theorem bound4156 : BoxMajorant Geometry.b4156 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4156.Widths)
  · have he : Geometry.b4156.half 1 false=Geometry.b4449 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4449
  · have he : Geometry.b4156.half 1 true=Geometry.b4450 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4450

theorem bound4155 : BoxMajorant Geometry.b4155 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4155.Widths)
  · have he : Geometry.b4155.half 1 false=Geometry.b4447 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4447
  · have he : Geometry.b4155.half 1 true=Geometry.b4448 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4448

theorem bound4154 : BoxMajorant Geometry.b4154 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4154.Widths)
  · have he : Geometry.b4154.half 1 false=Geometry.b4445 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4445
  · have he : Geometry.b4154.half 1 true=Geometry.b4446 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4446

theorem bound4153 : BoxMajorant Geometry.b4153 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4153 2 (by decide +kernel) x hx hd ho).elim

theorem bound3736 : BoxMajorant Geometry.b3736 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3736.Widths)
  · have he : Geometry.b3736.half 0 false=Geometry.b4155 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4155
  · have he : Geometry.b3736.half 0 true=Geometry.b4156 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4156

theorem bound3735 : BoxMajorant Geometry.b3735 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3735 2 (by decide +kernel) x hx hd ho).elim

theorem bound3734 : BoxMajorant Geometry.b3734 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3734.Widths)
  · have he : Geometry.b3734.half 0 false=Geometry.b4153 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4153
  · have he : Geometry.b3734.half 0 true=Geometry.b4154 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4154

theorem bound3733 : BoxMajorant Geometry.b3733 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3733 2 (by decide +kernel) x hx hd ho).elim

theorem bound3458 : BoxMajorant Geometry.b3458 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3458.Widths)
  · have he : Geometry.b3458.half 2 false=Geometry.b3735 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3735
  · have he : Geometry.b3458.half 2 true=Geometry.b3736 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3736

theorem bound3457 : BoxMajorant Geometry.b3457 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3457.Widths)
  · have he : Geometry.b3457.half 2 false=Geometry.b3733 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3733
  · have he : Geometry.b3457.half 2 true=Geometry.b3734 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3734

theorem bound3186 : BoxMajorant Geometry.b3186 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3186.Widths)
  · have he : Geometry.b3186.half 1 false=Geometry.b3457 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3457
  · have he : Geometry.b3186.half 1 true=Geometry.b3458 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3458

theorem bound3185 : BoxMajorant Geometry.b3185 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3185 2 (by decide +kernel) x hx hd ho).elim

theorem bound2800 : BoxMajorant Geometry.b2800 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2800.Widths)
  · have he : Geometry.b2800.half 0 false=Geometry.b3185 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3185
  · have he : Geometry.b2800.half 0 true=Geometry.b3186 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3186

end N7.Kernel.Cover
