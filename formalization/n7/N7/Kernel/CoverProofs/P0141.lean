import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0029
import N7.Kernel.CoverGeometry.G0030
import N7.Kernel.PositiveGroups.G0157
import N7.Kernel.PositiveGroups.G0200
import N7.Kernel.PositiveGroups.G0201
import N7.Kernel.PositiveGroups.G0240
import N7.Kernel.PositiveGroups.G0241
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1922 : BoxMajorant Geometry.b1922 := by
  exact PositiveLeaves.L696.bound

theorem bound1921 : BoxMajorant Geometry.b1921 := by
  exact PositiveLeaves.L697.bound

theorem bound1920 : BoxMajorant Geometry.b1920 := by
  exact PositiveLeaves.L698.bound

theorem bound1919 : BoxMajorant Geometry.b1919 := by
  exact PositiveLeaves.L699.bound

theorem bound1918 : BoxMajorant Geometry.b1918 := by
  exact PositiveLeaves.L700.bound

theorem bound1917 : BoxMajorant Geometry.b1917 := by
  exact PositiveLeaves.L701.bound

theorem bound1328 : BoxMajorant Geometry.b1328 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1328.Widths)
  · have he : Geometry.b1328.half 2 false=Geometry.b1921 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1921
  · have he : Geometry.b1328.half 2 true=Geometry.b1922 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1922

theorem bound1327 : BoxMajorant Geometry.b1327 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1327.Widths)
  · have he : Geometry.b1327.half 2 false=Geometry.b1919 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1919
  · have he : Geometry.b1327.half 2 true=Geometry.b1920 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1920

theorem bound1326 : BoxMajorant Geometry.b1326 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1326.Widths)
  · have he : Geometry.b1326.half 2 false=Geometry.b1917 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1917
  · have he : Geometry.b1326.half 2 true=Geometry.b1918 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1918

theorem bound1325 : BoxMajorant Geometry.b1325 := by
  exact PositiveLeaves.L702.bound

theorem bound952 : BoxMajorant Geometry.b952 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b952.Widths)
  · have he : Geometry.b952.half 1 false=Geometry.b1327 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1327
  · have he : Geometry.b952.half 1 true=Geometry.b1328 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1328

theorem bound951 : BoxMajorant Geometry.b951 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b951.Widths)
  · have he : Geometry.b951.half 1 false=Geometry.b1325 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1325
  · have he : Geometry.b951.half 1 true=Geometry.b1326 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1326

theorem bound660 : BoxMajorant Geometry.b660 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b660.Widths)
  · have he : Geometry.b660.half 0 false=Geometry.b951 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound951
  · have he : Geometry.b660.half 0 true=Geometry.b952 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound952

end N7.Kernel.Cover
