import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0030
import N7.Kernel.CoverGeometry.G0037
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverProofs.P0308
import N7.Kernel.CoverProofs.P0309
import N7.Kernel.CoverProofs.P0310
import N7.Kernel.CoverProofs.P0311
import N7.Kernel.CoverProofs.P0312
import N7.Kernel.CoverProofs.P0313
import N7.Kernel.CoverProofs.P0314
import N7.Kernel.CoverProofs.P0315
import N7.Kernel.CoverProofs.P0316
import N7.Kernel.CoverProofs.P0317
import N7.Kernel.PositiveGroups.G0199
import N7.Kernel.PositiveGroups.G0238
import N7.Kernel.PositiveGroups.G0240
import N7.Kernel.PositiveGroups.G0275
import N7.Kernel.PositiveGroups.G0276
import N7.Kernel.PositiveGroups.G0277
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2742 : BoxMajorant Geometry.b2742 := by
  exact PositiveLeaves.L654.bound

theorem bound2741 : BoxMajorant Geometry.b2741 := by
  exact PositiveLeaves.L655.bound

theorem bound2733 : BoxMajorant Geometry.b2733 := by
  exact PositiveLeaves.L681.bound

theorem bound2729 : BoxMajorant Geometry.b2729 := by
  exact PositiveLeaves.L690.bound

theorem bound2728 : BoxMajorant Geometry.b2728 := by
  exact PositiveLeaves.L693.bound

theorem bound2727 : BoxMajorant Geometry.b2727 := by
  exact PositiveLeaves.L694.bound

theorem bound2402 : BoxMajorant Geometry.b2402 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2402.Widths)
  · have he : Geometry.b2402.half 1 false=Geometry.b2741 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2741
  · have he : Geometry.b2402.half 1 true=Geometry.b2742 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2742

theorem bound2401 : BoxMajorant Geometry.b2401 := by
  exact PositiveLeaves.L656.bound

theorem bound2400 : BoxMajorant Geometry.b2400 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2400.Widths)
  · have he : Geometry.b2400.half 1 false=Geometry.b2739 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2739
  · have he : Geometry.b2400.half 1 true=Geometry.b2740 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2740

theorem bound2399 : BoxMajorant Geometry.b2399 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2399.Widths)
  · have he : Geometry.b2399.half 1 false=Geometry.b2737 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2737
  · have he : Geometry.b2399.half 1 true=Geometry.b2738 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2738

theorem bound2398 : BoxMajorant Geometry.b2398 := by
  exact PositiveLeaves.L673.bound

theorem bound2397 : BoxMajorant Geometry.b2397 := by
  exact PositiveLeaves.L674.bound

theorem bound2396 : BoxMajorant Geometry.b2396 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2396.Widths)
  · have he : Geometry.b2396.half 1 false=Geometry.b2735 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2735
  · have he : Geometry.b2396.half 1 true=Geometry.b2736 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2736

theorem bound2395 : BoxMajorant Geometry.b2395 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2395.Widths)
  · have he : Geometry.b2395.half 1 false=Geometry.b2733 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2733
  · have he : Geometry.b2395.half 1 true=Geometry.b2734 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2734

theorem bound2394 : BoxMajorant Geometry.b2394 := by
  exact PositiveLeaves.L682.bound

theorem bound2393 : BoxMajorant Geometry.b2393 := by
  exact PositiveLeaves.L683.bound

theorem bound2392 : BoxMajorant Geometry.b2392 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2392.Widths)
  · have he : Geometry.b2392.half 1 false=Geometry.b2731 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2731
  · have he : Geometry.b2392.half 1 true=Geometry.b2732 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2732

theorem bound2391 : BoxMajorant Geometry.b2391 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2391.Widths)
  · have he : Geometry.b2391.half 1 false=Geometry.b2729 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2729
  · have he : Geometry.b2391.half 1 true=Geometry.b2730 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2730

theorem bound2390 : BoxMajorant Geometry.b2390 := by
  exact PositiveLeaves.L691.bound

theorem bound2389 : BoxMajorant Geometry.b2389 := by
  exact PositiveLeaves.L692.bound

theorem bound2388 : BoxMajorant Geometry.b2388 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2388.Widths)
  · have he : Geometry.b2388.half 1 false=Geometry.b2727 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2727
  · have he : Geometry.b2388.half 1 true=Geometry.b2728 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2728

theorem bound2387 : BoxMajorant Geometry.b2387 := by
  exact PositiveLeaves.L695.bound

theorem bound1930 : BoxMajorant Geometry.b1930 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1930.Widths)
  · have he : Geometry.b1930.half 0 false=Geometry.b2401 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2401
  · have he : Geometry.b1930.half 0 true=Geometry.b2402 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2402

theorem bound1929 : BoxMajorant Geometry.b1929 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1929.Widths)
  · have he : Geometry.b1929.half 0 false=Geometry.b2399 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2399
  · have he : Geometry.b1929.half 0 true=Geometry.b2400 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2400

theorem bound1928 : BoxMajorant Geometry.b1928 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1928.Widths)
  · have he : Geometry.b1928.half 0 false=Geometry.b2397 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2397
  · have he : Geometry.b1928.half 0 true=Geometry.b2398 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2398

theorem bound1927 : BoxMajorant Geometry.b1927 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1927.Widths)
  · have he : Geometry.b1927.half 0 false=Geometry.b2395 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2395
  · have he : Geometry.b1927.half 0 true=Geometry.b2396 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2396

theorem bound1926 : BoxMajorant Geometry.b1926 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1926.Widths)
  · have he : Geometry.b1926.half 0 false=Geometry.b2393 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2393
  · have he : Geometry.b1926.half 0 true=Geometry.b2394 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2394

theorem bound1925 : BoxMajorant Geometry.b1925 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1925.Widths)
  · have he : Geometry.b1925.half 0 false=Geometry.b2391 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2391
  · have he : Geometry.b1925.half 0 true=Geometry.b2392 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2392

theorem bound1924 : BoxMajorant Geometry.b1924 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1924.Widths)
  · have he : Geometry.b1924.half 0 false=Geometry.b2389 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2389
  · have he : Geometry.b1924.half 0 true=Geometry.b2390 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2390

theorem bound1923 : BoxMajorant Geometry.b1923 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1923.Widths)
  · have he : Geometry.b1923.half 0 false=Geometry.b2387 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2387
  · have he : Geometry.b1923.half 0 true=Geometry.b2388 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2388

theorem bound1332 : BoxMajorant Geometry.b1332 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1332.Widths)
  · have he : Geometry.b1332.half 2 false=Geometry.b1929 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1929
  · have he : Geometry.b1332.half 2 true=Geometry.b1930 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1930

theorem bound1331 : BoxMajorant Geometry.b1331 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1331.Widths)
  · have he : Geometry.b1331.half 2 false=Geometry.b1927 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1927
  · have he : Geometry.b1331.half 2 true=Geometry.b1928 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1928

theorem bound1330 : BoxMajorant Geometry.b1330 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1330.Widths)
  · have he : Geometry.b1330.half 2 false=Geometry.b1925 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1925
  · have he : Geometry.b1330.half 2 true=Geometry.b1926 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1926

theorem bound1329 : BoxMajorant Geometry.b1329 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1329.Widths)
  · have he : Geometry.b1329.half 2 false=Geometry.b1923 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1923
  · have he : Geometry.b1329.half 2 true=Geometry.b1924 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1924

theorem bound954 : BoxMajorant Geometry.b954 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b954.Widths)
  · have he : Geometry.b954.half 1 false=Geometry.b1331 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1331
  · have he : Geometry.b954.half 1 true=Geometry.b1332 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1332

theorem bound953 : BoxMajorant Geometry.b953 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b953.Widths)
  · have he : Geometry.b953.half 1 false=Geometry.b1329 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1329
  · have he : Geometry.b953.half 1 true=Geometry.b1330 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1330

theorem bound661 : BoxMajorant Geometry.b661 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b661.Widths)
  · have he : Geometry.b661.half 0 false=Geometry.b953 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound953
  · have he : Geometry.b661.half 0 true=Geometry.b954 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound954

end N7.Kernel.Cover
