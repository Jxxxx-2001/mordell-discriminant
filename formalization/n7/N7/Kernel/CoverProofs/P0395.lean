import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.PositiveGroups.G0444
import N7.Kernel.PositiveGroups.G0445
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5074 : BoxMajorant Geometry.b5074 := by
  exact PositiveLeaves.L264.bound

theorem bound5073 : BoxMajorant Geometry.b5073 := by
  exact PositiveLeaves.L265.bound

theorem bound4693 : BoxMajorant Geometry.b4693 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4693.Widths)
  · have he : Geometry.b4693.half 2 false=Geometry.b5073 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5073
  · have he : Geometry.b4693.half 2 true=Geometry.b5074 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5074

end N7.Kernel.Cover
