import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0095
import N7.Kernel.PositiveGroups.G0137
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2072 : BoxMajorant Geometry.b2072 := by
  exact PositiveLeaves.L51.bound

theorem bound2071 : BoxMajorant Geometry.b2071 := by
  exact PositiveLeaves.L52.bound

theorem bound1426 : BoxMajorant Geometry.b1426 := by
  exact PositiveLeaves.L50.bound

theorem bound1425 : BoxMajorant Geometry.b1425 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1425.Widths)
  · have he : Geometry.b1425.half 2 false=Geometry.b2071 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2071
  · have he : Geometry.b1425.half 2 true=Geometry.b2072 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2072

theorem bound1016 : BoxMajorant Geometry.b1016 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1016.Widths)
  · have he : Geometry.b1016.half 1 false=Geometry.b1425 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1425
  · have he : Geometry.b1016.half 1 true=Geometry.b1426 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1426

end N7.Kernel.Cover
