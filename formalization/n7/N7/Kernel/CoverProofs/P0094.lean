import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.PositiveGroups.G0093
import N7.Kernel.PositiveGroups.G0133
import N7.Kernel.PositiveGroups.G0134
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2668 : BoxMajorant Geometry.b2668 := by
  exact PositiveLeaves.L1162.bound

theorem bound2667 : BoxMajorant Geometry.b2667 := by
  exact PositiveLeaves.L1163.bound

theorem bound2296 : BoxMajorant Geometry.b2296 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2296.Widths)
  · have he : Geometry.b2296.half 1 false=Geometry.b2667 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2667
  · have he : Geometry.b2296.half 1 true=Geometry.b2668 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2668

theorem bound2295 : BoxMajorant Geometry.b2295 := by
  exact PositiveLeaves.L1164.bound

theorem bound1690 : BoxMajorant Geometry.b1690 := by
  exact PositiveLeaves.L1161.bound

theorem bound1689 : BoxMajorant Geometry.b1689 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1689.Widths)
  · have he : Geometry.b1689.half 0 false=Geometry.b2295 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2295
  · have he : Geometry.b1689.half 0 true=Geometry.b2296 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2296

theorem bound1688 : BoxMajorant Geometry.b1688 := by
  exact PositiveLeaves.L1165.bound

theorem bound1687 : BoxMajorant Geometry.b1687 := by
  exact PositiveLeaves.L1166.bound

theorem bound1192 : BoxMajorant Geometry.b1192 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1192.Widths)
  · have he : Geometry.b1192.half 2 false=Geometry.b1689 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1689
  · have he : Geometry.b1192.half 2 true=Geometry.b1690 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1690

theorem bound1191 : BoxMajorant Geometry.b1191 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1191.Widths)
  · have he : Geometry.b1191.half 2 false=Geometry.b1687 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1687
  · have he : Geometry.b1191.half 2 true=Geometry.b1688 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1688

theorem bound868 : BoxMajorant Geometry.b868 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b868.Widths)
  · have he : Geometry.b868.half 1 false=Geometry.b1191 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1191
  · have he : Geometry.b868.half 1 true=Geometry.b1192 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1192

end N7.Kernel.Cover
