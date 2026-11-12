import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.PositiveGroups.G0481
import N7.Kernel.PositiveGroups.G0485
import N7.Kernel.PositiveGroups.G0486
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5668 : BoxMajorant Geometry.b5668 := by
  exact PositiveLeaves.L296.bound

theorem bound5667 : BoxMajorant Geometry.b5667 := by
  exact PositiveLeaves.L297.bound

theorem bound5620 : BoxMajorant Geometry.b5620 := by
  exact PositiveLeaves.L295.bound

theorem bound5619 : BoxMajorant Geometry.b5619 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5619.Widths)
  · have he : Geometry.b5619.half 2 false=Geometry.b5667 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5667
  · have he : Geometry.b5619.half 2 true=Geometry.b5668 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5668

theorem bound5585 : BoxMajorant Geometry.b5585 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5585.Widths)
  · have he : Geometry.b5585.half 1 false=Geometry.b5619 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5619
  · have he : Geometry.b5585.half 1 true=Geometry.b5620 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5620

end N7.Kernel.Cover
