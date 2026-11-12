import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0030
import N7.Kernel.PositiveGroups.G0156
import N7.Kernel.PositiveGroups.G0193
import N7.Kernel.PositiveGroups.G0234
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1976 : BoxMajorant Geometry.b1976 := by
  exact PositiveLeaves.L581.bound

theorem bound1975 : BoxMajorant Geometry.b1975 := by
  exact PositiveLeaves.L582.bound

theorem bound1360 : BoxMajorant Geometry.b1360 := by
  exact PositiveLeaves.L580.bound

theorem bound1359 : BoxMajorant Geometry.b1359 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1359.Widths)
  · have he : Geometry.b1359.half 2 false=Geometry.b1975 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1975
  · have he : Geometry.b1359.half 2 true=Geometry.b1976 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1976

theorem bound970 : BoxMajorant Geometry.b970 := by
  exact PositiveLeaves.L579.bound

theorem bound969 : BoxMajorant Geometry.b969 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b969.Widths)
  · have he : Geometry.b969.half 1 false=Geometry.b1359 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1359
  · have he : Geometry.b969.half 1 true=Geometry.b1360 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1360

theorem bound676 : BoxMajorant Geometry.b676 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b676.Widths)
  · have he : Geometry.b676.half 0 false=Geometry.b969 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound969
  · have he : Geometry.b676.half 0 true=Geometry.b970 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound970

end N7.Kernel.Cover
