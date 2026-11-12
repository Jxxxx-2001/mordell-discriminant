import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0030
import N7.Kernel.PositiveGroups.G0197
import N7.Kernel.PositiveGroups.G0198
import N7.Kernel.PositiveGroups.G0199
import N7.Kernel.PositiveGroups.G0237
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1952 : BoxMajorant Geometry.b1952 := by
  exact PositiveLeaves.L618.bound

theorem bound1951 : BoxMajorant Geometry.b1951 := by
  exact PositiveLeaves.L619.bound

theorem bound1950 : BoxMajorant Geometry.b1950 := by
  exact PositiveLeaves.L620.bound

theorem bound1949 : BoxMajorant Geometry.b1949 := by
  exact PositiveLeaves.L621.bound

theorem bound1948 : BoxMajorant Geometry.b1948 := by
  exact PositiveLeaves.L622.bound

theorem bound1947 : BoxMajorant Geometry.b1947 := by
  exact PositiveLeaves.L623.bound

theorem bound1946 : BoxMajorant Geometry.b1946 := by
  exact PositiveLeaves.L624.bound

theorem bound1945 : BoxMajorant Geometry.b1945 := by
  exact PositiveLeaves.L625.bound

theorem bound1344 : BoxMajorant Geometry.b1344 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1344.Widths)
  · have he : Geometry.b1344.half 2 false=Geometry.b1951 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1951
  · have he : Geometry.b1344.half 2 true=Geometry.b1952 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1952

theorem bound1343 : BoxMajorant Geometry.b1343 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1343.Widths)
  · have he : Geometry.b1343.half 2 false=Geometry.b1949 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1949
  · have he : Geometry.b1343.half 2 true=Geometry.b1950 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1950

theorem bound1342 : BoxMajorant Geometry.b1342 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1342.Widths)
  · have he : Geometry.b1342.half 2 false=Geometry.b1947 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1947
  · have he : Geometry.b1342.half 2 true=Geometry.b1948 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1948

theorem bound1341 : BoxMajorant Geometry.b1341 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1341.Widths)
  · have he : Geometry.b1341.half 2 false=Geometry.b1945 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1945
  · have he : Geometry.b1341.half 2 true=Geometry.b1946 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1946

theorem bound960 : BoxMajorant Geometry.b960 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b960.Widths)
  · have he : Geometry.b960.half 1 false=Geometry.b1343 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1343
  · have he : Geometry.b960.half 1 true=Geometry.b1344 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1344

theorem bound959 : BoxMajorant Geometry.b959 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b959.Widths)
  · have he : Geometry.b959.half 1 false=Geometry.b1341 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1341
  · have he : Geometry.b959.half 1 true=Geometry.b1342 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1342

theorem bound664 : BoxMajorant Geometry.b664 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b664.Widths)
  · have he : Geometry.b664.half 0 false=Geometry.b959 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound959
  · have he : Geometry.b664.half 0 true=Geometry.b960 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound960

end N7.Kernel.Cover
