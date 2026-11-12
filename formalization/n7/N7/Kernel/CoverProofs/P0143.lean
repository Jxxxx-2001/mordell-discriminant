import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0030
import N7.Kernel.PositiveGroups.G0156
import N7.Kernel.PositiveGroups.G0199
import N7.Kernel.PositiveGroups.G0239
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1936 : BoxMajorant Geometry.b1936 := by
  exact PositiveLeaves.L647.bound

theorem bound1935 : BoxMajorant Geometry.b1935 := by
  exact PositiveLeaves.L648.bound

theorem bound1934 : BoxMajorant Geometry.b1934 := by
  exact PositiveLeaves.L649.bound

theorem bound1933 : BoxMajorant Geometry.b1933 := by
  exact PositiveLeaves.L650.bound

theorem bound1932 : BoxMajorant Geometry.b1932 := by
  exact PositiveLeaves.L651.bound

theorem bound1931 : BoxMajorant Geometry.b1931 := by
  exact PositiveLeaves.L652.bound

theorem bound1336 : BoxMajorant Geometry.b1336 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1336.Widths)
  · have he : Geometry.b1336.half 2 false=Geometry.b1935 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1935
  · have he : Geometry.b1336.half 2 true=Geometry.b1936 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1936

theorem bound1335 : BoxMajorant Geometry.b1335 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1335.Widths)
  · have he : Geometry.b1335.half 2 false=Geometry.b1933 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1933
  · have he : Geometry.b1335.half 2 true=Geometry.b1934 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1934

theorem bound1334 : BoxMajorant Geometry.b1334 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1334.Widths)
  · have he : Geometry.b1334.half 2 false=Geometry.b1931 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1931
  · have he : Geometry.b1334.half 2 true=Geometry.b1932 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1932

theorem bound1333 : BoxMajorant Geometry.b1333 := by
  exact PositiveLeaves.L653.bound

theorem bound956 : BoxMajorant Geometry.b956 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b956.Widths)
  · have he : Geometry.b956.half 1 false=Geometry.b1335 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1335
  · have he : Geometry.b956.half 1 true=Geometry.b1336 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1336

theorem bound955 : BoxMajorant Geometry.b955 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b955.Widths)
  · have he : Geometry.b955.half 1 false=Geometry.b1333 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1333
  · have he : Geometry.b955.half 1 true=Geometry.b1334 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1334

theorem bound662 : BoxMajorant Geometry.b662 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b662.Widths)
  · have he : Geometry.b662.half 0 false=Geometry.b955 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound955
  · have he : Geometry.b662.half 0 true=Geometry.b956 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound956

end N7.Kernel.Cover
