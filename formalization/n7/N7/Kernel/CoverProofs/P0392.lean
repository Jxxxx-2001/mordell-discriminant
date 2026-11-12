import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.PositiveGroups.G0431
import N7.Kernel.PositiveGroups.G0449
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5070 : BoxMajorant Geometry.b5070 := by
  exact PositiveLeaves.L283.bound

theorem bound5069 : BoxMajorant Geometry.b5069 := by
  exact PositiveLeaves.L284.bound

theorem bound4690 : BoxMajorant Geometry.b4690 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4690.Widths)
  · have he : Geometry.b4690.half 2 false=Geometry.b5069 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5069
  · have he : Geometry.b4690.half 2 true=Geometry.b5070 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5070

theorem bound4689 : BoxMajorant Geometry.b4689 := by
  exact PositiveLeaves.L285.bound

theorem bound4420 : BoxMajorant Geometry.b4420 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4420.Widths)
  · have he : Geometry.b4420.half 1 false=Geometry.b4689 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4689
  · have he : Geometry.b4420.half 1 true=Geometry.b4690 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4690

end N7.Kernel.Cover
