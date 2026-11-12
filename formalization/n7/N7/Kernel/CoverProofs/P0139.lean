import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0029
import N7.Kernel.CoverGeometry.G0037
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.PositiveGroups.G0157
import N7.Kernel.PositiveGroups.G0201
import N7.Kernel.PositiveGroups.G0202
import N7.Kernel.PositiveGroups.G0203
import N7.Kernel.PositiveGroups.G0242
import N7.Kernel.PositiveGroups.G0243
import N7.Kernel.PositiveGroups.G0244
import N7.Kernel.PositiveGroups.G0277
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2722 : BoxMajorant Geometry.b2722 := by
  exact PositiveLeaves.L719.bound

theorem bound2721 : BoxMajorant Geometry.b2721 := by
  exact PositiveLeaves.L720.bound

theorem bound2380 : BoxMajorant Geometry.b2380 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2380.Widths)
  · have he : Geometry.b2380.half 1 false=Geometry.b2721 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2721
  · have he : Geometry.b2380.half 1 true=Geometry.b2722 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2722

theorem bound2379 : BoxMajorant Geometry.b2379 := by
  exact PositiveLeaves.L721.bound

theorem bound2378 : BoxMajorant Geometry.b2378 := by
  exact PositiveLeaves.L722.bound

theorem bound2377 : BoxMajorant Geometry.b2377 := by
  exact PositiveLeaves.L723.bound

theorem bound2376 : BoxMajorant Geometry.b2376 := by
  exact PositiveLeaves.L724.bound

theorem bound2375 : BoxMajorant Geometry.b2375 := by
  exact PositiveLeaves.L725.bound

theorem bound2374 : BoxMajorant Geometry.b2374 := by
  exact PositiveLeaves.L726.bound

theorem bound2373 : BoxMajorant Geometry.b2373 := by
  exact PositiveLeaves.L727.bound

theorem bound2372 : BoxMajorant Geometry.b2372 := by
  exact PositiveLeaves.L728.bound

theorem bound2371 : BoxMajorant Geometry.b2371 := by
  exact PositiveLeaves.L729.bound

theorem bound2370 : BoxMajorant Geometry.b2370 := by
  exact PositiveLeaves.L731.bound

theorem bound2369 : BoxMajorant Geometry.b2369 := by
  exact PositiveLeaves.L732.bound

theorem bound1908 : BoxMajorant Geometry.b1908 := by
  exact PositiveLeaves.L718.bound

theorem bound1907 : BoxMajorant Geometry.b1907 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1907.Widths)
  · have he : Geometry.b1907.half 0 false=Geometry.b2379 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2379
  · have he : Geometry.b1907.half 0 true=Geometry.b2380 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2380

theorem bound1906 : BoxMajorant Geometry.b1906 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1906.Widths)
  · have he : Geometry.b1906.half 0 false=Geometry.b2377 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2377
  · have he : Geometry.b1906.half 0 true=Geometry.b2378 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2378

theorem bound1905 : BoxMajorant Geometry.b1905 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1905.Widths)
  · have he : Geometry.b1905.half 0 false=Geometry.b2375 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2375
  · have he : Geometry.b1905.half 0 true=Geometry.b2376 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2376

theorem bound1904 : BoxMajorant Geometry.b1904 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1904.Widths)
  · have he : Geometry.b1904.half 0 false=Geometry.b2373 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2373
  · have he : Geometry.b1904.half 0 true=Geometry.b2374 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2374

theorem bound1903 : BoxMajorant Geometry.b1903 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1903.Widths)
  · have he : Geometry.b1903.half 0 false=Geometry.b2371 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2371
  · have he : Geometry.b1903.half 0 true=Geometry.b2372 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2372

theorem bound1902 : BoxMajorant Geometry.b1902 := by
  exact PositiveLeaves.L730.bound

theorem bound1901 : BoxMajorant Geometry.b1901 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1901.Widths)
  · have he : Geometry.b1901.half 0 false=Geometry.b2369 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2369
  · have he : Geometry.b1901.half 0 true=Geometry.b2370 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2370

theorem bound1320 : BoxMajorant Geometry.b1320 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1320.Widths)
  · have he : Geometry.b1320.half 2 false=Geometry.b1907 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1907
  · have he : Geometry.b1320.half 2 true=Geometry.b1908 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1908

theorem bound1319 : BoxMajorant Geometry.b1319 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1319.Widths)
  · have he : Geometry.b1319.half 2 false=Geometry.b1905 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1905
  · have he : Geometry.b1319.half 2 true=Geometry.b1906 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1906

theorem bound1318 : BoxMajorant Geometry.b1318 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1318.Widths)
  · have he : Geometry.b1318.half 2 false=Geometry.b1903 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1903
  · have he : Geometry.b1318.half 2 true=Geometry.b1904 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1904

theorem bound1317 : BoxMajorant Geometry.b1317 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1317.Widths)
  · have he : Geometry.b1317.half 2 false=Geometry.b1901 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1901
  · have he : Geometry.b1317.half 2 true=Geometry.b1902 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1902

theorem bound948 : BoxMajorant Geometry.b948 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b948.Widths)
  · have he : Geometry.b948.half 1 false=Geometry.b1319 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1319
  · have he : Geometry.b948.half 1 true=Geometry.b1320 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1320

theorem bound947 : BoxMajorant Geometry.b947 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b947.Widths)
  · have he : Geometry.b947.half 1 false=Geometry.b1317 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1317
  · have he : Geometry.b947.half 1 true=Geometry.b1318 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1318

theorem bound657 : BoxMajorant Geometry.b657 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b657.Widths)
  · have he : Geometry.b657.half 0 false=Geometry.b947 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound947
  · have he : Geometry.b657.half 0 true=Geometry.b948 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound948

end N7.Kernel.Cover
