import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.PositiveGroups.G0447
import N7.Kernel.PositiveGroups.G0460
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5530 : BoxMajorant Geometry.b5530 := by
  exact PositiveLeaves.L233.bound

theorem bound5529 : BoxMajorant Geometry.b5529 := by
  exact PositiveLeaves.L234.bound

theorem bound5386 : BoxMajorant Geometry.b5386 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5386.Widths)
  · have he : Geometry.b5386.half 2 false=Geometry.b5529 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5529
  · have he : Geometry.b5386.half 2 true=Geometry.b5530 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5530

theorem bound5385 : BoxMajorant Geometry.b5385 := by
  exact PositiveLeaves.L235.bound

theorem bound5270 : BoxMajorant Geometry.b5270 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5270.Widths)
  · have he : Geometry.b5270.half 1 false=Geometry.b5385 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5385
  · have he : Geometry.b5270.half 1 true=Geometry.b5386 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5386

theorem bound5269 : BoxMajorant Geometry.b5269 := by
  exact PositiveLeaves.L236.bound

theorem bound5084 : BoxMajorant Geometry.b5084 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5084.Widths)
  · have he : Geometry.b5084.half 0 false=Geometry.b5269 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5269
  · have he : Geometry.b5084.half 0 true=Geometry.b5270 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5270

end N7.Kernel.Cover
