import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.PositiveGroups.G0026
import N7.Kernel.PositiveGroups.G0046
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1548 : BoxMajorant Geometry.b1548 := by
  exact PositiveLeaves.L2381.bound

theorem bound1547 : BoxMajorant Geometry.b1547 := by
  exact PositiveLeaves.L2382.bound

theorem bound1102 : BoxMajorant Geometry.b1102 := by
  exact PositiveLeaves.L2380.bound

theorem bound1101 : BoxMajorant Geometry.b1101 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1101.Widths)
  · have he : Geometry.b1101.half 2 false=Geometry.b1547 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1547
  · have he : Geometry.b1101.half 2 true=Geometry.b1548 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1548

theorem bound800 : BoxMajorant Geometry.b800 := by
  exact PositiveLeaves.L2379.bound

theorem bound799 : BoxMajorant Geometry.b799 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b799.Widths)
  · have he : Geometry.b799.half 1 false=Geometry.b1101 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1101
  · have he : Geometry.b799.half 1 true=Geometry.b1102 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1102

theorem bound518 : BoxMajorant Geometry.b518 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b518.Widths)
  · have he : Geometry.b518.half 0 false=Geometry.b799 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound799
  · have he : Geometry.b518.half 0 true=Geometry.b800 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound800

end N7.Kernel.Cover
