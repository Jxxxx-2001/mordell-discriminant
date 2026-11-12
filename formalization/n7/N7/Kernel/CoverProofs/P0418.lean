import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.PositiveGroups.G0485
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5666 : BoxMajorant Geometry.b5666 := by
  exact PositiveLeaves.L299.bound

theorem bound5665 : BoxMajorant Geometry.b5665 := by
  exact PositiveLeaves.L300.bound

theorem bound5618 : BoxMajorant Geometry.b5618 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5618.Widths)
  · have he : Geometry.b5618.half 2 false=Geometry.b5665 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5665
  · have he : Geometry.b5618.half 2 true=Geometry.b5666 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5666

end N7.Kernel.Cover
