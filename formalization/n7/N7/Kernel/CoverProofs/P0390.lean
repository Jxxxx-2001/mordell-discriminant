import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverProofs.P0407
import N7.Kernel.CoverProofs.P0408
import N7.Kernel.CoverProofs.P0409
import N7.Kernel.CoverProofs.P0410
import N7.Kernel.CoverProofs.P0411
import N7.Kernel.PositiveGroups.G0431
import N7.Kernel.PositiveGroups.G0461
import N7.Kernel.PositiveGroups.G0467
import N7.Kernel.PositiveGroups.G0468
import N7.Kernel.PositiveGroups.G0469
import N7.Kernel.PositiveGroups.G0478
import N7.Kernel.PositiveGroups.G0479
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5575 : BoxMajorant Geometry.b5575 := by
  exact PositiveLeaves.L424.bound

theorem bound5573 : BoxMajorant Geometry.b5573 := by
  exact PositiveLeaves.L432.bound

theorem bound5517 : BoxMajorant Geometry.b5517 := by
  exact PositiveLeaves.L373.bound

theorem bound5516 : BoxMajorant Geometry.b5516 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5516.Widths)
  · have he : Geometry.b5516.half 0 false=Geometry.b5577 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5577
  · have he : Geometry.b5516.half 0 true=Geometry.b5578 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5578

theorem bound5515 : BoxMajorant Geometry.b5515 := by
  exact PositiveLeaves.L419.bound

theorem bound5514 : BoxMajorant Geometry.b5514 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5514.Widths)
  · have he : Geometry.b5514.half 0 false=Geometry.b5575 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5575
  · have he : Geometry.b5514.half 0 true=Geometry.b5576 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5576

theorem bound5513 : BoxMajorant Geometry.b5513 := by
  exact PositiveLeaves.L425.bound

theorem bound5512 : BoxMajorant Geometry.b5512 := by
  exact PositiveLeaves.L426.bound

theorem bound5511 : BoxMajorant Geometry.b5511 := by
  exact PositiveLeaves.L427.bound

theorem bound5510 : BoxMajorant Geometry.b5510 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5510.Widths)
  · have he : Geometry.b5510.half 0 false=Geometry.b5573 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5573
  · have he : Geometry.b5510.half 0 true=Geometry.b5574 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5574

theorem bound5509 : BoxMajorant Geometry.b5509 := by
  exact PositiveLeaves.L433.bound

theorem bound5508 : BoxMajorant Geometry.b5508 := by
  exact PositiveLeaves.L434.bound

theorem bound5507 : BoxMajorant Geometry.b5507 := by
  exact PositiveLeaves.L435.bound

theorem bound5506 : BoxMajorant Geometry.b5506 := by
  exact PositiveLeaves.L436.bound

theorem bound5505 : BoxMajorant Geometry.b5505 := by
  exact PositiveLeaves.L437.bound

theorem bound5378 : BoxMajorant Geometry.b5378 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5378.Widths)
  · have he : Geometry.b5378.half 2 false=Geometry.b5517 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5517
  · have he : Geometry.b5378.half 2 true=Geometry.b5518 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5518

theorem bound5377 : BoxMajorant Geometry.b5377 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5377.Widths)
  · have he : Geometry.b5377.half 2 false=Geometry.b5515 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5515
  · have he : Geometry.b5377.half 2 true=Geometry.b5516 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5516

theorem bound5376 : BoxMajorant Geometry.b5376 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5376.Widths)
  · have he : Geometry.b5376.half 2 false=Geometry.b5513 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5513
  · have he : Geometry.b5376.half 2 true=Geometry.b5514 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5514

theorem bound5375 : BoxMajorant Geometry.b5375 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5375.Widths)
  · have he : Geometry.b5375.half 2 false=Geometry.b5511 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5511
  · have he : Geometry.b5375.half 2 true=Geometry.b5512 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5512

theorem bound5374 : BoxMajorant Geometry.b5374 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5374.Widths)
  · have he : Geometry.b5374.half 2 false=Geometry.b5509 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5509
  · have he : Geometry.b5374.half 2 true=Geometry.b5510 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5510

theorem bound5373 : BoxMajorant Geometry.b5373 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5373.Widths)
  · have he : Geometry.b5373.half 2 false=Geometry.b5507 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5507
  · have he : Geometry.b5373.half 2 true=Geometry.b5508 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5508

theorem bound5372 : BoxMajorant Geometry.b5372 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5372.Widths)
  · have he : Geometry.b5372.half 2 false=Geometry.b5505 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5505
  · have he : Geometry.b5372.half 2 true=Geometry.b5506 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5506

theorem bound5371 : BoxMajorant Geometry.b5371 := by
  exact PositiveLeaves.L438.bound

theorem bound5264 : BoxMajorant Geometry.b5264 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5264.Widths)
  · have he : Geometry.b5264.half 1 false=Geometry.b5377 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5377
  · have he : Geometry.b5264.half 1 true=Geometry.b5378 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5378

theorem bound5263 : BoxMajorant Geometry.b5263 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5263.Widths)
  · have he : Geometry.b5263.half 1 false=Geometry.b5375 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5375
  · have he : Geometry.b5263.half 1 true=Geometry.b5376 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5376

theorem bound5262 : BoxMajorant Geometry.b5262 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5262.Widths)
  · have he : Geometry.b5262.half 1 false=Geometry.b5373 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5373
  · have he : Geometry.b5262.half 1 true=Geometry.b5374 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5374

theorem bound5261 : BoxMajorant Geometry.b5261 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5261.Widths)
  · have he : Geometry.b5261.half 1 false=Geometry.b5371 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5371
  · have he : Geometry.b5261.half 1 true=Geometry.b5372 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5372

theorem bound5064 : BoxMajorant Geometry.b5064 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5064.Widths)
  · have he : Geometry.b5064.half 0 false=Geometry.b5263 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5263
  · have he : Geometry.b5064.half 0 true=Geometry.b5264 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5264

theorem bound5063 : BoxMajorant Geometry.b5063 := by
  exact PositiveLeaves.L428.bound

theorem bound5062 : BoxMajorant Geometry.b5062 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5062.Widths)
  · have he : Geometry.b5062.half 0 false=Geometry.b5261 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5261
  · have he : Geometry.b5062.half 0 true=Geometry.b5262 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5262

theorem bound5061 : BoxMajorant Geometry.b5061 := by
  exact PositiveLeaves.L439.bound

theorem bound4686 : BoxMajorant Geometry.b4686 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4686.Widths)
  · have he : Geometry.b4686.half 2 false=Geometry.b5063 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5063
  · have he : Geometry.b4686.half 2 true=Geometry.b5064 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5064

theorem bound4685 : BoxMajorant Geometry.b4685 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4685.Widths)
  · have he : Geometry.b4685.half 2 false=Geometry.b5061 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5061
  · have he : Geometry.b4685.half 2 true=Geometry.b5062 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5062

theorem bound4417 : BoxMajorant Geometry.b4417 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4417.Widths)
  · have he : Geometry.b4417.half 1 false=Geometry.b4685 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4685
  · have he : Geometry.b4417.half 1 true=Geometry.b4686 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4686

end N7.Kernel.Cover
