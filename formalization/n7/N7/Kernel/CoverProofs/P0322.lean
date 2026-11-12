import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverProofs.P0387
import N7.Kernel.CoverProofs.P0388
import N7.Kernel.CoverProofs.P0389
import N7.Kernel.CoverProofs.P0390
import N7.Kernel.CoverProofs.P0391
import N7.Kernel.CoverProofs.P0392
import N7.Kernel.CoverProofs.P0393
import N7.Kernel.PositiveGroups.G0332
import N7.Kernel.PositiveGroups.G0360
import N7.Kernel.PositiveGroups.G0361
import N7.Kernel.PositiveGroups.G0393
import N7.Kernel.PositiveGroups.G0394
import N7.Kernel.PositiveGroups.G0412
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4677 : BoxMajorant Geometry.b4677 := by
  exact PositiveLeaves.L463.bound

theorem bound4422 : BoxMajorant Geometry.b4422 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4422 0 (by decide +kernel) x hx hd ho).elim

theorem bound4421 : BoxMajorant Geometry.b4421 := by
  exact PositiveLeaves.L281.bound

theorem bound4419 : BoxMajorant Geometry.b4419 := by
  exact PositiveLeaves.L286.bound

theorem bound4416 : BoxMajorant Geometry.b4416 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4416 0 (by decide +kernel) x hx hd ho).elim

theorem bound4412 : BoxMajorant Geometry.b4412 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4412.Widths)
  · have he : Geometry.b4412.half 1 false=Geometry.b4677 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4677
  · have he : Geometry.b4412.half 1 true=Geometry.b4678 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4678

theorem bound4411 : BoxMajorant Geometry.b4411 := by
  exact PositiveLeaves.L464.bound

theorem bound4118 : BoxMajorant Geometry.b4118 := by
  exact PositiveLeaves.L277.bound

theorem bound4117 : BoxMajorant Geometry.b4117 := by
  exact PositiveLeaves.L278.bound

theorem bound4116 : BoxMajorant Geometry.b4116 := by
  exact PositiveLeaves.L279.bound

theorem bound4115 : BoxMajorant Geometry.b4115 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4115.Widths)
  · have he : Geometry.b4115.half 0 false=Geometry.b4421 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4421
  · have he : Geometry.b4115.half 0 true=Geometry.b4422 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4422

theorem bound4114 : BoxMajorant Geometry.b4114 := by
  exact PositiveLeaves.L282.bound

theorem bound4113 : BoxMajorant Geometry.b4113 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4113.Widths)
  · have he : Geometry.b4113.half 0 false=Geometry.b4419 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4419
  · have he : Geometry.b4113.half 0 true=Geometry.b4420 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4420

theorem bound4112 : BoxMajorant Geometry.b4112 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4112.Widths)
  · have he : Geometry.b4112.half 0 false=Geometry.b4417 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4417
  · have he : Geometry.b4112.half 0 true=Geometry.b4418 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4418

theorem bound4111 : BoxMajorant Geometry.b4111 := by
  exact PositiveLeaves.L440.bound

theorem bound4110 : BoxMajorant Geometry.b4110 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4110.Widths)
  · have he : Geometry.b4110.half 0 false=Geometry.b4415 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4415
  · have he : Geometry.b4110.half 0 true=Geometry.b4416 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4416

theorem bound4109 : BoxMajorant Geometry.b4109 := by
  exact PositiveLeaves.L445.bound

theorem bound4108 : BoxMajorant Geometry.b4108 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4108.Widths)
  · have he : Geometry.b4108.half 0 false=Geometry.b4413 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4413
  · have he : Geometry.b4108.half 0 true=Geometry.b4414 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4414

theorem bound4107 : BoxMajorant Geometry.b4107 := by
  exact PositiveLeaves.L460.bound

theorem bound4106 : BoxMajorant Geometry.b4106 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4106.Widths)
  · have he : Geometry.b4106.half 0 false=Geometry.b4411 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4411
  · have he : Geometry.b4106.half 0 true=Geometry.b4412 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4412

theorem bound4105 : BoxMajorant Geometry.b4105 := by
  exact PositiveLeaves.L465.bound

theorem bound3710 : BoxMajorant Geometry.b3710 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3710.Widths)
  · have he : Geometry.b3710.half 2 false=Geometry.b4117 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4117
  · have he : Geometry.b3710.half 2 true=Geometry.b4118 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4118

theorem bound3709 : BoxMajorant Geometry.b3709 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3709.Widths)
  · have he : Geometry.b3709.half 2 false=Geometry.b4115 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4115
  · have he : Geometry.b3709.half 2 true=Geometry.b4116 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4116

theorem bound3708 : BoxMajorant Geometry.b3708 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3708.Widths)
  · have he : Geometry.b3708.half 2 false=Geometry.b4113 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4113
  · have he : Geometry.b3708.half 2 true=Geometry.b4114 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4114

theorem bound3707 : BoxMajorant Geometry.b3707 := by
  exact PositiveLeaves.L287.bound

theorem bound3706 : BoxMajorant Geometry.b3706 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3706.Widths)
  · have he : Geometry.b3706.half 2 false=Geometry.b4111 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4111
  · have he : Geometry.b3706.half 2 true=Geometry.b4112 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4112

theorem bound3705 : BoxMajorant Geometry.b3705 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3705.Widths)
  · have he : Geometry.b3705.half 2 false=Geometry.b4109 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4109
  · have he : Geometry.b3705.half 2 true=Geometry.b4110 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4110

theorem bound3704 : BoxMajorant Geometry.b3704 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3704.Widths)
  · have he : Geometry.b3704.half 2 false=Geometry.b4107 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4107
  · have he : Geometry.b3704.half 2 true=Geometry.b4108 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4108

theorem bound3703 : BoxMajorant Geometry.b3703 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3703.Widths)
  · have he : Geometry.b3703.half 2 false=Geometry.b4105 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4105
  · have he : Geometry.b3703.half 2 true=Geometry.b4106 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4106

theorem bound3440 : BoxMajorant Geometry.b3440 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3440.Widths)
  · have he : Geometry.b3440.half 1 false=Geometry.b3709 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3709
  · have he : Geometry.b3440.half 1 true=Geometry.b3710 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3710

theorem bound3439 : BoxMajorant Geometry.b3439 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3439.Widths)
  · have he : Geometry.b3439.half 1 false=Geometry.b3707 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3707
  · have he : Geometry.b3439.half 1 true=Geometry.b3708 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3708

theorem bound3438 : BoxMajorant Geometry.b3438 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3438.Widths)
  · have he : Geometry.b3438.half 1 false=Geometry.b3705 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3705
  · have he : Geometry.b3438.half 1 true=Geometry.b3706 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3706

theorem bound3437 : BoxMajorant Geometry.b3437 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3437.Widths)
  · have he : Geometry.b3437.half 1 false=Geometry.b3703 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3703
  · have he : Geometry.b3437.half 1 true=Geometry.b3704 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3704

theorem bound3156 : BoxMajorant Geometry.b3156 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3156.Widths)
  · have he : Geometry.b3156.half 0 false=Geometry.b3439 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3439
  · have he : Geometry.b3156.half 0 true=Geometry.b3440 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3440

theorem bound3155 : BoxMajorant Geometry.b3155 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3155.Widths)
  · have he : Geometry.b3155.half 0 false=Geometry.b3437 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3437
  · have he : Geometry.b3155.half 0 true=Geometry.b3438 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3438

theorem bound2760 : BoxMajorant Geometry.b2760 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2760.Widths)
  · have he : Geometry.b2760.half 2 false=Geometry.b3155 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3155
  · have he : Geometry.b2760.half 2 true=Geometry.b3156 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3156

end N7.Kernel.Cover
