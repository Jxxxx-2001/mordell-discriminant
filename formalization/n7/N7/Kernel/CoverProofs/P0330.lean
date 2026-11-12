import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.PositiveGroups.G0257
import N7.Kernel.PositiveGroups.G0285
import N7.Kernel.PositiveGroups.G0308
import N7.Kernel.PositiveGroups.G0331
import N7.Kernel.PositiveGroups.G0332
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4718 : BoxMajorant Geometry.b4718 := by
  exact PositiveLeaves.L160.bound

theorem bound4717 : BoxMajorant Geometry.b4717 := by
  exact PositiveLeaves.L161.bound

theorem bound4440 : BoxMajorant Geometry.b4440 := by
  exact PositiveLeaves.L159.bound

theorem bound4439 : BoxMajorant Geometry.b4439 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4439.Widths)
  · have he : Geometry.b4439.half 1 false=Geometry.b4717 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4717
  · have he : Geometry.b4439.half 1 true=Geometry.b4718 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4718

theorem bound4148 : BoxMajorant Geometry.b4148 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4148.Widths)
  · have he : Geometry.b4148.half 0 false=Geometry.b4439 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4439
  · have he : Geometry.b4148.half 0 true=Geometry.b4440 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4440

theorem bound4147 : BoxMajorant Geometry.b4147 := by
  exact PositiveLeaves.L162.bound

theorem bound3728 : BoxMajorant Geometry.b3728 := by
  exact PositiveLeaves.L158.bound

theorem bound3727 : BoxMajorant Geometry.b3727 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3727.Widths)
  · have he : Geometry.b3727.half 2 false=Geometry.b4147 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4147
  · have he : Geometry.b3727.half 2 true=Geometry.b4148 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4148

theorem bound3452 : BoxMajorant Geometry.b3452 := by
  exact PositiveLeaves.L157.bound

theorem bound3451 : BoxMajorant Geometry.b3451 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3451.Widths)
  · have he : Geometry.b3451.half 1 false=Geometry.b3727 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3727
  · have he : Geometry.b3451.half 1 true=Geometry.b3728 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3728

theorem bound3172 : BoxMajorant Geometry.b3172 := by
  exact PositiveLeaves.L156.bound

theorem bound3171 : BoxMajorant Geometry.b3171 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3171.Widths)
  · have he : Geometry.b3171.half 0 false=Geometry.b3451 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3451
  · have he : Geometry.b3171.half 0 true=Geometry.b3452 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3452

theorem bound2773 : BoxMajorant Geometry.b2773 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2773.Widths)
  · have he : Geometry.b2773.half 2 false=Geometry.b3171 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3171
  · have he : Geometry.b2773.half 2 true=Geometry.b3172 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3172

end N7.Kernel.Cover
