import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0302
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3126 : BoxMajorant Geometry.b3126 := by
  exact PositiveLeaves.L677.bound

theorem bound3125 : BoxMajorant Geometry.b3125 := by
  exact PositiveLeaves.L678.bound

theorem bound2735 : BoxMajorant Geometry.b2735 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2735.Widths)
  · have he : Geometry.b2735.half 2 false=Geometry.b3125 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3125
  · have he : Geometry.b2735.half 2 true=Geometry.b3126 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3126

end N7.Kernel.Cover
