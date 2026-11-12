import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverProofs.P0400
import N7.Kernel.CoverProofs.P0401
import N7.Kernel.CoverProofs.P0402
import N7.Kernel.CoverProofs.P0403
import N7.Kernel.CoverProofs.P0404
import N7.Kernel.CoverProofs.P0405
import N7.Kernel.CoverProofs.P0406
import N7.Kernel.PositiveGroups.G0308
import N7.Kernel.PositiveGroups.G0392
import N7.Kernel.PositiveGroups.G0393
import N7.Kernel.PositiveGroups.G0412
import N7.Kernel.PositiveGroups.G0430
import N7.Kernel.PositiveGroups.G0431
import N7.Kernel.PositiveGroups.G0445
import N7.Kernel.PositiveGroups.G0446
import N7.Kernel.PositiveGroups.G0447
import N7.Kernel.PositiveGroups.G0448
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5092 : BoxMajorant Geometry.b5092 := by
  exact PositiveLeaves.L212.bound

theorem bound5091 : BoxMajorant Geometry.b5091 := by
  exact PositiveLeaves.L213.bound

theorem bound5089 : BoxMajorant Geometry.b5089 := by
  exact PositiveLeaves.L221.bound

theorem bound5087 : BoxMajorant Geometry.b5087 := by
  exact PositiveLeaves.L230.bound

theorem bound5086 : BoxMajorant Geometry.b5086 := by
  exact PositiveLeaves.L231.bound

theorem bound5085 : BoxMajorant Geometry.b5085 := by
  exact PositiveLeaves.L232.bound

theorem bound5083 : BoxMajorant Geometry.b5083 := by
  exact PositiveLeaves.L237.bound

theorem bound4714 : BoxMajorant Geometry.b4714 := by
  exact PositiveLeaves.L187.bound

theorem bound4713 : BoxMajorant Geometry.b4713 := by
  exact PositiveLeaves.L188.bound

theorem bound4712 : BoxMajorant Geometry.b4712 := by
  exact PositiveLeaves.L190.bound

theorem bound4708 : BoxMajorant Geometry.b4708 := by
  exact PositiveLeaves.L208.bound

theorem bound4706 : BoxMajorant Geometry.b4706 := by
  exact PositiveLeaves.L211.bound

theorem bound4705 : BoxMajorant Geometry.b4705 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4705.Widths)
  · have he : Geometry.b4705.half 2 false=Geometry.b5091 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5091
  · have he : Geometry.b4705.half 2 true=Geometry.b5092 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5092

theorem bound4704 : BoxMajorant Geometry.b4704 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4704.Widths)
  · have he : Geometry.b4704.half 2 false=Geometry.b5089 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5089
  · have he : Geometry.b4704.half 2 true=Geometry.b5090 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5090

theorem bound4703 : BoxMajorant Geometry.b4703 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4703.Widths)
  · have he : Geometry.b4703.half 2 false=Geometry.b5087 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5087
  · have he : Geometry.b4703.half 2 true=Geometry.b5088 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5088

theorem bound4702 : BoxMajorant Geometry.b4702 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4702.Widths)
  · have he : Geometry.b4702.half 2 false=Geometry.b5085 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5085
  · have he : Geometry.b4702.half 2 true=Geometry.b5086 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5086

theorem bound4701 : BoxMajorant Geometry.b4701 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4701.Widths)
  · have he : Geometry.b4701.half 2 false=Geometry.b5083 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5083
  · have he : Geometry.b4701.half 2 true=Geometry.b5084 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5084

theorem bound4436 : BoxMajorant Geometry.b4436 := by
  exact PositiveLeaves.L186.bound

theorem bound4435 : BoxMajorant Geometry.b4435 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4435.Widths)
  · have he : Geometry.b4435.half 1 false=Geometry.b4713 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4713
  · have he : Geometry.b4435.half 1 true=Geometry.b4714 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4714

theorem bound4434 : BoxMajorant Geometry.b4434 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4434.Widths)
  · have he : Geometry.b4434.half 1 false=Geometry.b4711 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4711
  · have he : Geometry.b4434.half 1 true=Geometry.b4712 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4712

theorem bound4433 : BoxMajorant Geometry.b4433 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4433.Widths)
  · have he : Geometry.b4433.half 1 false=Geometry.b4709 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4709
  · have he : Geometry.b4433.half 1 true=Geometry.b4710 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4710

theorem bound4432 : BoxMajorant Geometry.b4432 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4432.Widths)
  · have he : Geometry.b4432.half 1 false=Geometry.b4707 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4707
  · have he : Geometry.b4432.half 1 true=Geometry.b4708 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4708

theorem bound4431 : BoxMajorant Geometry.b4431 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4431.Widths)
  · have he : Geometry.b4431.half 1 false=Geometry.b4705 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4705
  · have he : Geometry.b4431.half 1 true=Geometry.b4706 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4706

theorem bound4430 : BoxMajorant Geometry.b4430 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4430.Widths)
  · have he : Geometry.b4430.half 1 false=Geometry.b4703 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4703
  · have he : Geometry.b4430.half 1 true=Geometry.b4704 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4704

theorem bound4429 : BoxMajorant Geometry.b4429 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4429.Widths)
  · have he : Geometry.b4429.half 1 false=Geometry.b4701 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4701
  · have he : Geometry.b4429.half 1 true=Geometry.b4702 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4702

theorem bound4144 : BoxMajorant Geometry.b4144 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4144.Widths)
  · have he : Geometry.b4144.half 0 false=Geometry.b4435 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4435
  · have he : Geometry.b4144.half 0 true=Geometry.b4436 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4436

theorem bound4143 : BoxMajorant Geometry.b4143 := by
  exact PositiveLeaves.L189.bound

theorem bound4142 : BoxMajorant Geometry.b4142 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4142.Widths)
  · have he : Geometry.b4142.half 0 false=Geometry.b4433 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4433
  · have he : Geometry.b4142.half 0 true=Geometry.b4434 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4434

theorem bound4141 : BoxMajorant Geometry.b4141 := by
  exact PositiveLeaves.L207.bound

theorem bound4140 : BoxMajorant Geometry.b4140 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4140.Widths)
  · have he : Geometry.b4140.half 0 false=Geometry.b4431 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4431
  · have he : Geometry.b4140.half 0 true=Geometry.b4432 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4432

theorem bound4139 : BoxMajorant Geometry.b4139 := by
  exact PositiveLeaves.L214.bound

theorem bound4138 : BoxMajorant Geometry.b4138 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4138.Widths)
  · have he : Geometry.b4138.half 0 false=Geometry.b4429 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4429
  · have he : Geometry.b4138.half 0 true=Geometry.b4430 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4430

theorem bound4137 : BoxMajorant Geometry.b4137 := by
  exact PositiveLeaves.L238.bound

theorem bound3724 : BoxMajorant Geometry.b3724 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3724.Widths)
  · have he : Geometry.b3724.half 2 false=Geometry.b4143 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4143
  · have he : Geometry.b3724.half 2 true=Geometry.b4144 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4144

theorem bound3723 : BoxMajorant Geometry.b3723 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3723.Widths)
  · have he : Geometry.b3723.half 2 false=Geometry.b4141 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4141
  · have he : Geometry.b3723.half 2 true=Geometry.b4142 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4142

theorem bound3722 : BoxMajorant Geometry.b3722 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3722.Widths)
  · have he : Geometry.b3722.half 2 false=Geometry.b4139 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4139
  · have he : Geometry.b3722.half 2 true=Geometry.b4140 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4140

theorem bound3721 : BoxMajorant Geometry.b3721 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3721.Widths)
  · have he : Geometry.b3721.half 2 false=Geometry.b4137 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4137
  · have he : Geometry.b3721.half 2 true=Geometry.b4138 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4138

theorem bound3448 : BoxMajorant Geometry.b3448 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3448.Widths)
  · have he : Geometry.b3448.half 1 false=Geometry.b3723 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3723
  · have he : Geometry.b3448.half 1 true=Geometry.b3724 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3724

theorem bound3447 : BoxMajorant Geometry.b3447 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3447.Widths)
  · have he : Geometry.b3447.half 1 false=Geometry.b3721 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3721
  · have he : Geometry.b3447.half 1 true=Geometry.b3722 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3722

theorem bound3162 : BoxMajorant Geometry.b3162 := by
  exact PositiveLeaves.L185.bound

theorem bound3161 : BoxMajorant Geometry.b3161 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3161.Widths)
  · have he : Geometry.b3161.half 0 false=Geometry.b3447 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3447
  · have he : Geometry.b3161.half 0 true=Geometry.b3448 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3448

theorem bound2765 : BoxMajorant Geometry.b2765 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2765.Widths)
  · have he : Geometry.b2765.half 2 false=Geometry.b3161 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3161
  · have he : Geometry.b2765.half 2 true=Geometry.b3162 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3162

end N7.Kernel.Cover
