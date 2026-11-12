import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverGeometry.G0092
import N7.Kernel.PositiveGroups.G0497
import N7.Kernel.PositiveGroups.G0499
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5888 : BoxMajorant Geometry.b5888 := by
  exact PositiveLeaves.L405.bound

theorem bound5887 : BoxMajorant Geometry.b5887 := by
  exact PositiveLeaves.L406.bound

theorem bound5850 : BoxMajorant Geometry.b5850 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5850.Widths)
  · have he : Geometry.b5850.half 2 false=Geometry.b5887 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5887
  · have he : Geometry.b5850.half 2 true=Geometry.b5888 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5888

theorem bound5849 : BoxMajorant Geometry.b5849 := by
  exact PositiveLeaves.L407.bound

theorem bound5818 : BoxMajorant Geometry.b5818 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5818.Widths)
  · have he : Geometry.b5818.half 1 false=Geometry.b5849 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5849
  · have he : Geometry.b5818.half 1 true=Geometry.b5850 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5850

end N7.Kernel.Cover
