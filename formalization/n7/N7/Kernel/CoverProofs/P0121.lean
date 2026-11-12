import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.PositiveGroups.G0055
import N7.Kernel.PositiveGroups.G0056
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1814 : BoxMajorant Geometry.b1814 := by
  exact PositiveLeaves.L863.bound

theorem bound1813 : BoxMajorant Geometry.b1813 := by
  exact PositiveLeaves.L864.bound

theorem bound1262 : BoxMajorant Geometry.b1262 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1262.Widths)
  · have he : Geometry.b1262.half 2 false=Geometry.b1813 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1813
  · have he : Geometry.b1262.half 2 true=Geometry.b1814 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1814

theorem bound1261 : BoxMajorant Geometry.b1261 := by
  exact PositiveLeaves.L865.bound

theorem bound912 : BoxMajorant Geometry.b912 := by
  exact PositiveLeaves.L862.bound

theorem bound911 : BoxMajorant Geometry.b911 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b911.Widths)
  · have he : Geometry.b911.half 1 false=Geometry.b1261 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1261
  · have he : Geometry.b911.half 1 true=Geometry.b1262 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1262

theorem bound625 : BoxMajorant Geometry.b625 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b625.Widths)
  · have he : Geometry.b625.half 0 false=Geometry.b911 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound911
  · have he : Geometry.b625.half 0 true=Geometry.b912 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound912

end N7.Kernel.Cover
