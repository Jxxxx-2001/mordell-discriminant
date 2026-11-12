import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0061
import N7.Kernel.PositiveGroups.G0094
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2086 : BoxMajorant Geometry.b2086 := by
  exact PositiveLeaves.L28.bound

theorem bound2085 : BoxMajorant Geometry.b2085 := by
  exact PositiveLeaves.L29.bound

theorem bound1436 : BoxMajorant Geometry.b1436 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1436.Widths)
  · have he : Geometry.b1436.half 2 false=Geometry.b2085 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2085
  · have he : Geometry.b1436.half 2 true=Geometry.b2086 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2086

theorem bound1435 : BoxMajorant Geometry.b1435 := by
  exact PositiveLeaves.L30.bound

theorem bound1021 : BoxMajorant Geometry.b1021 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1021.Widths)
  · have he : Geometry.b1021.half 1 false=Geometry.b1435 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1435
  · have he : Geometry.b1021.half 1 true=Geometry.b1436 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1436

end N7.Kernel.Cover
