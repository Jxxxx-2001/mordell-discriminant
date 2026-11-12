import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.PositiveGroups.G0032
import N7.Kernel.PositiveGroups.G0059
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1676 : BoxMajorant Geometry.b1676 := by
  exact PositiveLeaves.L1181.bound

theorem bound1675 : BoxMajorant Geometry.b1675 := by
  exact PositiveLeaves.L1182.bound

theorem bound1184 : BoxMajorant Geometry.b1184 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1184.Widths)
  · have he : Geometry.b1184.half 2 false=Geometry.b1675 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1675
  · have he : Geometry.b1184.half 2 true=Geometry.b1676 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1676

theorem bound1183 : BoxMajorant Geometry.b1183 := by
  exact PositiveLeaves.L1183.bound

theorem bound863 : BoxMajorant Geometry.b863 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b863.Widths)
  · have he : Geometry.b863.half 1 false=Geometry.b1183 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1183
  · have he : Geometry.b863.half 1 true=Geometry.b1184 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1184

end N7.Kernel.Cover
