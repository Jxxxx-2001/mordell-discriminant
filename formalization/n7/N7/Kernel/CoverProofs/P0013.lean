import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.PositiveGroups.G0001
import N7.Kernel.PositiveGroups.G0003
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound148 : BoxMajorant Geometry.b148 := by
  exact PositiveLeaves.L1186.bound

theorem bound147 : BoxMajorant Geometry.b147 := by
  exact PositiveLeaves.L1187.bound

theorem bound86 : BoxMajorant Geometry.b86 := by
  exact PositiveLeaves.L1185.bound

theorem bound85 : BoxMajorant Geometry.b85 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b85.Widths)
  · have he : Geometry.b85.half 2 false=Geometry.b147 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound147
  · have he : Geometry.b85.half 2 true=Geometry.b148 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound148

theorem bound46 : BoxMajorant Geometry.b46 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b46.Widths)
  · have he : Geometry.b46.half 1 false=Geometry.b85 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound85
  · have he : Geometry.b46.half 1 true=Geometry.b86 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound86

end N7.Kernel.Cover
