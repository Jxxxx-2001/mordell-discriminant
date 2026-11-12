import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.PositiveGroups.G0279
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3414 : BoxMajorant Geometry.b3414 := by
  exact PositiveLeaves.L935.bound

theorem bound3413 : BoxMajorant Geometry.b3413 := by
  exact PositiveLeaves.L936.bound

theorem bound3092 : BoxMajorant Geometry.b3092 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3092.Widths)
  · have he : Geometry.b3092.half 0 false=Geometry.b3413 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3413
  · have he : Geometry.b3092.half 0 true=Geometry.b3414 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3414

end N7.Kernel.Cover
