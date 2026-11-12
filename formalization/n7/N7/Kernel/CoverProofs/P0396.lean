import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.PositiveGroups.G0445
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5076 : BoxMajorant Geometry.b5076 := by
  exact PositiveLeaves.L262.bound

theorem bound5075 : BoxMajorant Geometry.b5075 := by
  exact PositiveLeaves.L263.bound

theorem bound4694 : BoxMajorant Geometry.b4694 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4694.Widths)
  · have he : Geometry.b4694.half 2 false=Geometry.b5075 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5075
  · have he : Geometry.b4694.half 2 true=Geometry.b5076 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5076

end N7.Kernel.Cover
