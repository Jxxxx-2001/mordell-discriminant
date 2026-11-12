import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverProofs.P0052
import N7.Kernel.CoverProofs.P0053
import N7.Kernel.CoverProofs.P0054
import N7.Kernel.CoverProofs.P0055
import N7.Kernel.CoverProofs.P0056
import N7.Kernel.CoverProofs.P0057
import N7.Kernel.CoverProofs.P0058
import N7.Kernel.CoverProofs.P0059
import N7.Kernel.CoverProofs.P0060
import N7.Kernel.CoverProofs.P0061
import N7.Kernel.CoverProofs.P0062
import N7.Kernel.PositiveGroups.G0002
import N7.Kernel.PositiveGroups.G0004
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound816 : BoxMajorant Geometry.b816 := by
  exact PositiveLeaves.L2258.bound

theorem bound813 : BoxMajorant Geometry.b813 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b813 2 (by decide +kernel) x hx hd ho).elim

theorem bound803 : BoxMajorant Geometry.b803 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b803 2 (by decide +kernel) x hx hd ho).elim

theorem bound536 : BoxMajorant Geometry.b536 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b536.Widths)
  · have he : Geometry.b536.half 0 false=Geometry.b815 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound815
  · have he : Geometry.b536.half 0 true=Geometry.b816 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound816

theorem bound535 : BoxMajorant Geometry.b535 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b535.Widths)
  · have he : Geometry.b535.half 0 false=Geometry.b813 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound813
  · have he : Geometry.b535.half 0 true=Geometry.b814 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound814

theorem bound534 : BoxMajorant Geometry.b534 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b534.Widths)
  · have he : Geometry.b534.half 0 false=Geometry.b811 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound811
  · have he : Geometry.b534.half 0 true=Geometry.b812 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound812

theorem bound533 : BoxMajorant Geometry.b533 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b533 2 (by decide +kernel) x hx hd ho).elim

theorem bound532 : BoxMajorant Geometry.b532 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b532.Widths)
  · have he : Geometry.b532.half 0 false=Geometry.b809 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound809
  · have he : Geometry.b532.half 0 true=Geometry.b810 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound810

theorem bound531 : BoxMajorant Geometry.b531 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b531 2 (by decide +kernel) x hx hd ho).elim

theorem bound530 : BoxMajorant Geometry.b530 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b530.Widths)
  · have he : Geometry.b530.half 0 false=Geometry.b807 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound807
  · have he : Geometry.b530.half 0 true=Geometry.b808 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound808

theorem bound529 : BoxMajorant Geometry.b529 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b529 2 (by decide +kernel) x hx hd ho).elim

theorem bound528 : BoxMajorant Geometry.b528 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b528.Widths)
  · have he : Geometry.b528.half 0 false=Geometry.b805 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound805
  · have he : Geometry.b528.half 0 true=Geometry.b806 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound806

theorem bound527 : BoxMajorant Geometry.b527 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b527 2 (by decide +kernel) x hx hd ho).elim

theorem bound526 : BoxMajorant Geometry.b526 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b526.Widths)
  · have he : Geometry.b526.half 0 false=Geometry.b803 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound803
  · have he : Geometry.b526.half 0 true=Geometry.b804 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound804

theorem bound525 : BoxMajorant Geometry.b525 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b525 2 (by decide +kernel) x hx hd ho).elim

theorem bound342 : BoxMajorant Geometry.b342 := by
  exact PositiveLeaves.L2257.bound

theorem bound341 : BoxMajorant Geometry.b341 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b341.Widths)
  · have he : Geometry.b341.half 2 false=Geometry.b535 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound535
  · have he : Geometry.b341.half 2 true=Geometry.b536 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound536

theorem bound340 : BoxMajorant Geometry.b340 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b340.Widths)
  · have he : Geometry.b340.half 2 false=Geometry.b533 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound533
  · have he : Geometry.b340.half 2 true=Geometry.b534 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound534

theorem bound339 : BoxMajorant Geometry.b339 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b339.Widths)
  · have he : Geometry.b339.half 2 false=Geometry.b531 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound531
  · have he : Geometry.b339.half 2 true=Geometry.b532 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound532

theorem bound338 : BoxMajorant Geometry.b338 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b338.Widths)
  · have he : Geometry.b338.half 2 false=Geometry.b529 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound529
  · have he : Geometry.b338.half 2 true=Geometry.b530 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound530

theorem bound337 : BoxMajorant Geometry.b337 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b337.Widths)
  · have he : Geometry.b337.half 2 false=Geometry.b527 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound527
  · have he : Geometry.b337.half 2 true=Geometry.b528 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound528

theorem bound336 : BoxMajorant Geometry.b336 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b336.Widths)
  · have he : Geometry.b336.half 2 false=Geometry.b525 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound525
  · have he : Geometry.b336.half 2 true=Geometry.b526 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound526

theorem bound335 : BoxMajorant Geometry.b335 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b335 2 (by decide +kernel) x hx hd ho).elim

theorem bound214 : BoxMajorant Geometry.b214 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b214.Widths)
  · have he : Geometry.b214.half 1 false=Geometry.b341 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound341
  · have he : Geometry.b214.half 1 true=Geometry.b342 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound342

theorem bound213 : BoxMajorant Geometry.b213 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b213.Widths)
  · have he : Geometry.b213.half 1 false=Geometry.b339 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound339
  · have he : Geometry.b213.half 1 true=Geometry.b340 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound340

theorem bound212 : BoxMajorant Geometry.b212 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b212.Widths)
  · have he : Geometry.b212.half 1 false=Geometry.b337 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound337
  · have he : Geometry.b212.half 1 true=Geometry.b338 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound338

theorem bound211 : BoxMajorant Geometry.b211 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b211.Widths)
  · have he : Geometry.b211.half 1 false=Geometry.b335 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound335
  · have he : Geometry.b211.half 1 true=Geometry.b336 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound336

theorem bound126 : BoxMajorant Geometry.b126 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b126.Widths)
  · have he : Geometry.b126.half 0 false=Geometry.b213 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound213
  · have he : Geometry.b126.half 0 true=Geometry.b214 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound214

theorem bound125 : BoxMajorant Geometry.b125 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b125 2 (by decide +kernel) x hx hd ho).elim

theorem bound124 : BoxMajorant Geometry.b124 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b124.Widths)
  · have he : Geometry.b124.half 0 false=Geometry.b211 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound211
  · have he : Geometry.b124.half 0 true=Geometry.b212 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound212

theorem bound123 : BoxMajorant Geometry.b123 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b123 2 (by decide +kernel) x hx hd ho).elim

theorem bound70 : BoxMajorant Geometry.b70 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b70.Widths)
  · have he : Geometry.b70.half 2 false=Geometry.b125 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound125
  · have he : Geometry.b70.half 2 true=Geometry.b126 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound126

theorem bound69 : BoxMajorant Geometry.b69 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b69.Widths)
  · have he : Geometry.b69.half 2 false=Geometry.b123 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound123
  · have he : Geometry.b69.half 2 true=Geometry.b124 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound124

theorem bound36 : BoxMajorant Geometry.b36 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b36.Widths)
  · have he : Geometry.b36.half 1 false=Geometry.b69 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound69
  · have he : Geometry.b36.half 1 true=Geometry.b70 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound70

end N7.Kernel.Cover
