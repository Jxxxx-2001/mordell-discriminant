import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.PositiveGroups.G0059
import N7.Kernel.PositiveGroups.G0060
import N7.Kernel.PositiveGroups.G0094
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1680 : BoxMajorant Geometry.b1680 := by
  exact PositiveLeaves.L1177.bound

theorem bound1679 : BoxMajorant Geometry.b1679 := by
  exact PositiveLeaves.L1178.bound

theorem bound1678 : BoxMajorant Geometry.b1678 := by
  exact PositiveLeaves.L1179.bound

theorem bound1677 : BoxMajorant Geometry.b1677 := by
  exact PositiveLeaves.L1180.bound

theorem bound1186 : BoxMajorant Geometry.b1186 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1186.Widths)
  · have he : Geometry.b1186.half 2 false=Geometry.b1679 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1679
  · have he : Geometry.b1186.half 2 true=Geometry.b1680 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1680

theorem bound1185 : BoxMajorant Geometry.b1185 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1185.Widths)
  · have he : Geometry.b1185.half 2 false=Geometry.b1677 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1677
  · have he : Geometry.b1185.half 2 true=Geometry.b1678 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1678

theorem bound864 : BoxMajorant Geometry.b864 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b864.Widths)
  · have he : Geometry.b864.half 1 false=Geometry.b1185 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1185
  · have he : Geometry.b864.half 1 true=Geometry.b1186 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1186

end N7.Kernel.Cover
