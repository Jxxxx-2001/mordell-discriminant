import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.PositiveGroups.G0306
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3412 : BoxMajorant Geometry.b3412 := by
  exact PositiveLeaves.L966.bound

theorem bound3411 : BoxMajorant Geometry.b3411 := by
  exact PositiveLeaves.L967.bound

theorem bound3078 : BoxMajorant Geometry.b3078 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3078.Widths)
  · have he : Geometry.b3078.half 0 false=Geometry.b3411 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3411
  · have he : Geometry.b3078.half 0 true=Geometry.b3412 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3412

end N7.Kernel.Cover
