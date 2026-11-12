import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.PositiveGroups.G0432
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5050 : BoxMajorant Geometry.b5050 := by
  exact PositiveLeaves.L461.bound

theorem bound5049 : BoxMajorant Geometry.b5049 := by
  exact PositiveLeaves.L462.bound

theorem bound4678 : BoxMajorant Geometry.b4678 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4678.Widths)
  · have he : Geometry.b4678.half 2 false=Geometry.b5049 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5049
  · have he : Geometry.b4678.half 2 true=Geometry.b5050 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5050

end N7.Kernel.Cover
