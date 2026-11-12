import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0004
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverProofs.P0026
import N7.Kernel.CoverProofs.P0027
import N7.Kernel.CoverProofs.P0028
import N7.Kernel.CoverProofs.P0029
import N7.Kernel.CoverProofs.P0030
import N7.Kernel.CoverProofs.P0031
import N7.Kernel.CoverProofs.P0032
import N7.Kernel.CoverProofs.P0033
import N7.Kernel.CoverProofs.P0034
import N7.Kernel.CoverProofs.P0035
import N7.Kernel.CoverProofs.P0036
import N7.Kernel.CoverProofs.P0037
import N7.Kernel.CoverProofs.P0038
import N7.Kernel.CoverProofs.P0039
import N7.Kernel.CoverProofs.P0040
import N7.Kernel.CoverProofs.P0041
import N7.Kernel.CoverProofs.P0042
import N7.Kernel.CoverProofs.P0043
import N7.Kernel.PositiveGroups.G0011
import N7.Kernel.PositiveGroups.G0012
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound749 : BoxMajorant Geometry.b749 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b749 2 (by decide +kernel) x hx hd ho).elim

theorem bound503 : BoxMajorant Geometry.b503 := by
  exact PositiveLeaves.L2438.bound

theorem bound501 : BoxMajorant Geometry.b501 := by
  exact PositiveLeaves.L2451.bound

theorem bound495 : BoxMajorant Geometry.b495 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b495 2 (by decide +kernel) x hx hd ho).elim

theorem bound493 : BoxMajorant Geometry.b493 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b493 2 (by decide +kernel) x hx hd ho).elim

theorem bound491 : BoxMajorant Geometry.b491 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b491 2 (by decide +kernel) x hx hd ho).elim

theorem bound482 : BoxMajorant Geometry.b482 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b482.Widths)
  · have he : Geometry.b482.half 0 false=Geometry.b749 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound749
  · have he : Geometry.b482.half 0 true=Geometry.b750 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound750

theorem bound481 : BoxMajorant Geometry.b481 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b481 2 (by decide +kernel) x hx hd ho).elim

theorem bound320 : BoxMajorant Geometry.b320 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b320.Widths)
  · have he : Geometry.b320.half 2 false=Geometry.b503 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound503
  · have he : Geometry.b320.half 2 true=Geometry.b504 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound504

theorem bound319 : BoxMajorant Geometry.b319 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b319.Widths)
  · have he : Geometry.b319.half 2 false=Geometry.b501 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound501
  · have he : Geometry.b319.half 2 true=Geometry.b502 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound502

theorem bound318 : BoxMajorant Geometry.b318 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b318.Widths)
  · have he : Geometry.b318.half 2 false=Geometry.b499 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound499
  · have he : Geometry.b318.half 2 true=Geometry.b500 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound500

theorem bound317 : BoxMajorant Geometry.b317 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b317.Widths)
  · have he : Geometry.b317.half 2 false=Geometry.b497 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound497
  · have he : Geometry.b317.half 2 true=Geometry.b498 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound498

theorem bound316 : BoxMajorant Geometry.b316 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b316.Widths)
  · have he : Geometry.b316.half 2 false=Geometry.b495 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound495
  · have he : Geometry.b316.half 2 true=Geometry.b496 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound496

theorem bound315 : BoxMajorant Geometry.b315 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b315.Widths)
  · have he : Geometry.b315.half 2 false=Geometry.b493 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound493
  · have he : Geometry.b315.half 2 true=Geometry.b494 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound494

theorem bound314 : BoxMajorant Geometry.b314 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b314.Widths)
  · have he : Geometry.b314.half 2 false=Geometry.b491 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound491
  · have he : Geometry.b314.half 2 true=Geometry.b492 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound492

theorem bound313 : BoxMajorant Geometry.b313 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b313 2 (by decide +kernel) x hx hd ho).elim

theorem bound312 : BoxMajorant Geometry.b312 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b312.Widths)
  · have he : Geometry.b312.half 2 false=Geometry.b489 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound489
  · have he : Geometry.b312.half 2 true=Geometry.b490 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound490

theorem bound311 : BoxMajorant Geometry.b311 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b311.Widths)
  · have he : Geometry.b311.half 2 false=Geometry.b487 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound487
  · have he : Geometry.b311.half 2 true=Geometry.b488 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound488

theorem bound310 : BoxMajorant Geometry.b310 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b310.Widths)
  · have he : Geometry.b310.half 2 false=Geometry.b485 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound485
  · have he : Geometry.b310.half 2 true=Geometry.b486 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound486

theorem bound309 : BoxMajorant Geometry.b309 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b309.Widths)
  · have he : Geometry.b309.half 2 false=Geometry.b483 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound483
  · have he : Geometry.b309.half 2 true=Geometry.b484 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound484

theorem bound308 : BoxMajorant Geometry.b308 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b308.Widths)
  · have he : Geometry.b308.half 2 false=Geometry.b481 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound481
  · have he : Geometry.b308.half 2 true=Geometry.b482 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound482

theorem bound307 : BoxMajorant Geometry.b307 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b307 2 (by decide +kernel) x hx hd ho).elim

theorem bound200 : BoxMajorant Geometry.b200 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b200.Widths)
  · have he : Geometry.b200.half 1 false=Geometry.b319 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound319
  · have he : Geometry.b200.half 1 true=Geometry.b320 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound320

theorem bound199 : BoxMajorant Geometry.b199 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b199.Widths)
  · have he : Geometry.b199.half 1 false=Geometry.b317 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound317
  · have he : Geometry.b199.half 1 true=Geometry.b318 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound318

theorem bound198 : BoxMajorant Geometry.b198 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b198.Widths)
  · have he : Geometry.b198.half 1 false=Geometry.b315 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound315
  · have he : Geometry.b198.half 1 true=Geometry.b316 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound316

theorem bound197 : BoxMajorant Geometry.b197 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b197.Widths)
  · have he : Geometry.b197.half 1 false=Geometry.b313 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound313
  · have he : Geometry.b197.half 1 true=Geometry.b314 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound314

theorem bound196 : BoxMajorant Geometry.b196 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b196.Widths)
  · have he : Geometry.b196.half 1 false=Geometry.b311 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound311
  · have he : Geometry.b196.half 1 true=Geometry.b312 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound312

theorem bound195 : BoxMajorant Geometry.b195 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b195.Widths)
  · have he : Geometry.b195.half 1 false=Geometry.b309 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound309
  · have he : Geometry.b195.half 1 true=Geometry.b310 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound310

theorem bound194 : BoxMajorant Geometry.b194 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b194.Widths)
  · have he : Geometry.b194.half 1 false=Geometry.b307 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound307
  · have he : Geometry.b194.half 1 true=Geometry.b308 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound308

theorem bound193 : BoxMajorant Geometry.b193 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b193 2 (by decide +kernel) x hx hd ho).elim

theorem bound116 : BoxMajorant Geometry.b116 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b116.Widths)
  · have he : Geometry.b116.half 0 false=Geometry.b199 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound199
  · have he : Geometry.b116.half 0 true=Geometry.b200 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound200

theorem bound115 : BoxMajorant Geometry.b115 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b115.Widths)
  · have he : Geometry.b115.half 0 false=Geometry.b197 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound197
  · have he : Geometry.b115.half 0 true=Geometry.b198 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound198

theorem bound114 : BoxMajorant Geometry.b114 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b114.Widths)
  · have he : Geometry.b114.half 0 false=Geometry.b195 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound195
  · have he : Geometry.b114.half 0 true=Geometry.b196 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound196

theorem bound113 : BoxMajorant Geometry.b113 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b113.Widths)
  · have he : Geometry.b113.half 0 false=Geometry.b193 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound193
  · have he : Geometry.b113.half 0 true=Geometry.b194 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound194

theorem bound64 : BoxMajorant Geometry.b64 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b64.Widths)
  · have he : Geometry.b64.half 2 false=Geometry.b115 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound115
  · have he : Geometry.b64.half 2 true=Geometry.b116 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound116

theorem bound63 : BoxMajorant Geometry.b63 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b63.Widths)
  · have he : Geometry.b63.half 2 false=Geometry.b113 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound113
  · have he : Geometry.b63.half 2 true=Geometry.b114 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound114

theorem bound33 : BoxMajorant Geometry.b33 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b33.Widths)
  · have he : Geometry.b33.half 1 false=Geometry.b63 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound63
  · have he : Geometry.b33.half 1 true=Geometry.b64 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound64

end N7.Kernel.Cover
