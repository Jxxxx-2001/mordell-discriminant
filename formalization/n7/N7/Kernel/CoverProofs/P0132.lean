import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0029
import N7.Kernel.PositiveGroups.G0158
import N7.Kernel.PositiveGroups.G0159
import N7.Kernel.PositiveGroups.G0160
import N7.Kernel.PositiveGroups.G0208
import N7.Kernel.PositiveGroups.G0209
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1864 : BoxMajorant Geometry.b1864 := by
  exact PositiveLeaves.L782.bound

theorem bound1863 : BoxMajorant Geometry.b1863 := by
  exact PositiveLeaves.L783.bound

theorem bound1862 : BoxMajorant Geometry.b1862 := by
  exact PositiveLeaves.L784.bound

theorem bound1861 : BoxMajorant Geometry.b1861 := by
  exact PositiveLeaves.L785.bound

theorem bound1860 : BoxMajorant Geometry.b1860 := by
  exact PositiveLeaves.L786.bound

theorem bound1859 : BoxMajorant Geometry.b1859 := by
  exact PositiveLeaves.L787.bound

theorem bound1858 : BoxMajorant Geometry.b1858 := by
  exact PositiveLeaves.L788.bound

theorem bound1857 : BoxMajorant Geometry.b1857 := by
  exact PositiveLeaves.L789.bound

theorem bound1294 : BoxMajorant Geometry.b1294 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1294.Widths)
  · have he : Geometry.b1294.half 2 false=Geometry.b1863 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1863
  · have he : Geometry.b1294.half 2 true=Geometry.b1864 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1864

theorem bound1293 : BoxMajorant Geometry.b1293 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1293.Widths)
  · have he : Geometry.b1293.half 2 false=Geometry.b1861 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1861
  · have he : Geometry.b1293.half 2 true=Geometry.b1862 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1862

theorem bound1292 : BoxMajorant Geometry.b1292 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1292.Widths)
  · have he : Geometry.b1292.half 2 false=Geometry.b1859 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1859
  · have he : Geometry.b1292.half 2 true=Geometry.b1860 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1860

theorem bound1291 : BoxMajorant Geometry.b1291 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1291.Widths)
  · have he : Geometry.b1291.half 2 false=Geometry.b1857 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1857
  · have he : Geometry.b1291.half 2 true=Geometry.b1858 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1858

theorem bound934 : BoxMajorant Geometry.b934 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b934.Widths)
  · have he : Geometry.b934.half 1 false=Geometry.b1293 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1293
  · have he : Geometry.b934.half 1 true=Geometry.b1294 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1294

theorem bound933 : BoxMajorant Geometry.b933 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b933.Widths)
  · have he : Geometry.b933.half 1 false=Geometry.b1291 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1291
  · have he : Geometry.b933.half 1 true=Geometry.b1292 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1292

theorem bound645 : BoxMajorant Geometry.b645 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b645.Widths)
  · have he : Geometry.b645.half 0 false=Geometry.b933 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound933
  · have he : Geometry.b645.half 0 true=Geometry.b934 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound934

end N7.Kernel.Cover
