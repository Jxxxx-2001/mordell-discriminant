import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.PositiveGroups.G0090
import N7.Kernel.PositiveGroups.G0131
import N7.Kernel.PositiveGroups.G0132
import N7.Kernel.PositiveGroups.G0133
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1734 : BoxMajorant Geometry.b1734 := by
  exact PositiveLeaves.L1103.bound

theorem bound1733 : BoxMajorant Geometry.b1733 := by
  exact PositiveLeaves.L1104.bound

theorem bound1732 : BoxMajorant Geometry.b1732 := by
  exact PositiveLeaves.L1105.bound

theorem bound1731 : BoxMajorant Geometry.b1731 := by
  exact PositiveLeaves.L1106.bound

theorem bound1730 : BoxMajorant Geometry.b1730 := by
  exact PositiveLeaves.L1107.bound

theorem bound1729 : BoxMajorant Geometry.b1729 := by
  exact PositiveLeaves.L1108.bound

theorem bound1728 : BoxMajorant Geometry.b1728 := by
  exact PositiveLeaves.L1109.bound

theorem bound1727 : BoxMajorant Geometry.b1727 := by
  exact PositiveLeaves.L1110.bound

theorem bound1216 : BoxMajorant Geometry.b1216 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1216.Widths)
  · have he : Geometry.b1216.half 2 false=Geometry.b1733 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1733
  · have he : Geometry.b1216.half 2 true=Geometry.b1734 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1734

theorem bound1215 : BoxMajorant Geometry.b1215 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1215.Widths)
  · have he : Geometry.b1215.half 2 false=Geometry.b1731 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1731
  · have he : Geometry.b1215.half 2 true=Geometry.b1732 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1732

theorem bound1214 : BoxMajorant Geometry.b1214 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1214.Widths)
  · have he : Geometry.b1214.half 2 false=Geometry.b1729 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1729
  · have he : Geometry.b1214.half 2 true=Geometry.b1730 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1730

theorem bound1213 : BoxMajorant Geometry.b1213 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1213.Widths)
  · have he : Geometry.b1213.half 2 false=Geometry.b1727 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1727
  · have he : Geometry.b1213.half 2 true=Geometry.b1728 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1728

theorem bound880 : BoxMajorant Geometry.b880 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b880.Widths)
  · have he : Geometry.b880.half 1 false=Geometry.b1215 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1215
  · have he : Geometry.b880.half 1 true=Geometry.b1216 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1216

theorem bound879 : BoxMajorant Geometry.b879 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b879.Widths)
  · have he : Geometry.b879.half 1 false=Geometry.b1213 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1213
  · have he : Geometry.b879.half 1 true=Geometry.b1214 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1214

theorem bound602 : BoxMajorant Geometry.b602 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b602.Widths)
  · have he : Geometry.b602.half 0 false=Geometry.b879 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound879
  · have he : Geometry.b602.half 0 true=Geometry.b880 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound880

end N7.Kernel.Cover
