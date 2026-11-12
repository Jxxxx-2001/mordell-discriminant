import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0030
import N7.Kernel.PositiveGroups.G0193
import N7.Kernel.PositiveGroups.G0194
import N7.Kernel.PositiveGroups.G0233
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1974 : BoxMajorant Geometry.b1974 := by
  exact PositiveLeaves.L584.bound

theorem bound1973 : BoxMajorant Geometry.b1973 := by
  exact PositiveLeaves.L585.bound

theorem bound1972 : BoxMajorant Geometry.b1972 := by
  exact PositiveLeaves.L586.bound

theorem bound1971 : BoxMajorant Geometry.b1971 := by
  exact PositiveLeaves.L587.bound

theorem bound1970 : BoxMajorant Geometry.b1970 := by
  exact PositiveLeaves.L588.bound

theorem bound1969 : BoxMajorant Geometry.b1969 := by
  exact PositiveLeaves.L589.bound

theorem bound1968 : BoxMajorant Geometry.b1968 := by
  exact PositiveLeaves.L590.bound

theorem bound1967 : BoxMajorant Geometry.b1967 := by
  exact PositiveLeaves.L591.bound

theorem bound1358 : BoxMajorant Geometry.b1358 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1358.Widths)
  · have he : Geometry.b1358.half 2 false=Geometry.b1973 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1973
  · have he : Geometry.b1358.half 2 true=Geometry.b1974 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1974

theorem bound1357 : BoxMajorant Geometry.b1357 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1357.Widths)
  · have he : Geometry.b1357.half 2 false=Geometry.b1971 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1971
  · have he : Geometry.b1357.half 2 true=Geometry.b1972 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1972

theorem bound1356 : BoxMajorant Geometry.b1356 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1356.Widths)
  · have he : Geometry.b1356.half 2 false=Geometry.b1969 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1969
  · have he : Geometry.b1356.half 2 true=Geometry.b1970 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1970

theorem bound1355 : BoxMajorant Geometry.b1355 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1355.Widths)
  · have he : Geometry.b1355.half 2 false=Geometry.b1967 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1967
  · have he : Geometry.b1355.half 2 true=Geometry.b1968 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1968

theorem bound968 : BoxMajorant Geometry.b968 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b968.Widths)
  · have he : Geometry.b968.half 1 false=Geometry.b1357 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1357
  · have he : Geometry.b968.half 1 true=Geometry.b1358 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1358

theorem bound967 : BoxMajorant Geometry.b967 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b967.Widths)
  · have he : Geometry.b967.half 1 false=Geometry.b1355 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1355
  · have he : Geometry.b967.half 1 true=Geometry.b1356 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1356

theorem bound674 : BoxMajorant Geometry.b674 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b674.Widths)
  · have he : Geometry.b674.half 0 false=Geometry.b967 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound967
  · have he : Geometry.b674.half 0 true=Geometry.b968 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound968

end N7.Kernel.Cover
