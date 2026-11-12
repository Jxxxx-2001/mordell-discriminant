import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0030
import N7.Kernel.CoverGeometry.G0037
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverProofs.P0318
import N7.Kernel.PositiveGroups.G0197
import N7.Kernel.PositiveGroups.G0236
import N7.Kernel.PositiveGroups.G0237
import N7.Kernel.PositiveGroups.G0273
import N7.Kernel.PositiveGroups.G0274
import N7.Kernel.PositiveGroups.G0275
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3140 : BoxMajorant Geometry.b3140 := by
  exact PositiveLeaves.L635.bound

theorem bound3139 : BoxMajorant Geometry.b3139 := by
  exact PositiveLeaves.L636.bound

theorem bound3138 : BoxMajorant Geometry.b3138 := by
  exact PositiveLeaves.L644.bound

theorem bound3137 : BoxMajorant Geometry.b3137 := by
  exact PositiveLeaves.L645.bound

theorem bound2750 : BoxMajorant Geometry.b2750 := by
  exact PositiveLeaves.L630.bound

theorem bound2748 : BoxMajorant Geometry.b2748 := by
  exact PositiveLeaves.L634.bound

theorem bound2747 : BoxMajorant Geometry.b2747 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2747.Widths)
  · have he : Geometry.b2747.half 2 false=Geometry.b3139 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3139
  · have he : Geometry.b2747.half 2 true=Geometry.b3140 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3140

theorem bound2746 : BoxMajorant Geometry.b2746 := by
  exact PositiveLeaves.L640.bound

theorem bound2745 : BoxMajorant Geometry.b2745 := by
  exact PositiveLeaves.L641.bound

theorem bound2744 : BoxMajorant Geometry.b2744 := by
  exact PositiveLeaves.L643.bound

theorem bound2743 : BoxMajorant Geometry.b2743 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2743.Widths)
  · have he : Geometry.b2743.half 2 false=Geometry.b3137 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3137
  · have he : Geometry.b2743.half 2 true=Geometry.b3138 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3138

theorem bound2412 : BoxMajorant Geometry.b2412 := by
  exact PositiveLeaves.L628.bound

theorem bound2411 : BoxMajorant Geometry.b2411 := by
  exact PositiveLeaves.L629.bound

theorem bound2410 : BoxMajorant Geometry.b2410 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2410.Widths)
  · have he : Geometry.b2410.half 1 false=Geometry.b2749 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2749
  · have he : Geometry.b2410.half 1 true=Geometry.b2750 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2750

theorem bound2409 : BoxMajorant Geometry.b2409 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2409.Widths)
  · have he : Geometry.b2409.half 1 false=Geometry.b2747 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2747
  · have he : Geometry.b2409.half 1 true=Geometry.b2748 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2748

theorem bound2408 : BoxMajorant Geometry.b2408 := by
  exact PositiveLeaves.L637.bound

theorem bound2407 : BoxMajorant Geometry.b2407 := by
  exact PositiveLeaves.L638.bound

theorem bound2406 : BoxMajorant Geometry.b2406 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2406.Widths)
  · have he : Geometry.b2406.half 1 false=Geometry.b2745 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2745
  · have he : Geometry.b2406.half 1 true=Geometry.b2746 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2746

theorem bound2405 : BoxMajorant Geometry.b2405 := by
  exact PositiveLeaves.L642.bound

theorem bound2404 : BoxMajorant Geometry.b2404 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2404.Widths)
  · have he : Geometry.b2404.half 1 false=Geometry.b2743 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2743
  · have he : Geometry.b2404.half 1 true=Geometry.b2744 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2744

theorem bound2403 : BoxMajorant Geometry.b2403 := by
  exact PositiveLeaves.L646.bound

theorem bound1944 : BoxMajorant Geometry.b1944 := by
  exact PositiveLeaves.L626.bound

theorem bound1943 : BoxMajorant Geometry.b1943 := by
  exact PositiveLeaves.L627.bound

theorem bound1942 : BoxMajorant Geometry.b1942 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1942.Widths)
  · have he : Geometry.b1942.half 0 false=Geometry.b2411 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2411
  · have he : Geometry.b1942.half 0 true=Geometry.b2412 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2412

theorem bound1941 : BoxMajorant Geometry.b1941 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1941.Widths)
  · have he : Geometry.b1941.half 0 false=Geometry.b2409 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2409
  · have he : Geometry.b1941.half 0 true=Geometry.b2410 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2410

theorem bound1940 : BoxMajorant Geometry.b1940 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1940.Widths)
  · have he : Geometry.b1940.half 0 false=Geometry.b2407 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2407
  · have he : Geometry.b1940.half 0 true=Geometry.b2408 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2408

theorem bound1939 : BoxMajorant Geometry.b1939 := by
  exact PositiveLeaves.L639.bound

theorem bound1938 : BoxMajorant Geometry.b1938 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1938.Widths)
  · have he : Geometry.b1938.half 0 false=Geometry.b2405 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2405
  · have he : Geometry.b1938.half 0 true=Geometry.b2406 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2406

theorem bound1937 : BoxMajorant Geometry.b1937 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1937.Widths)
  · have he : Geometry.b1937.half 0 false=Geometry.b2403 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2403
  · have he : Geometry.b1937.half 0 true=Geometry.b2404 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2404

theorem bound1340 : BoxMajorant Geometry.b1340 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1340.Widths)
  · have he : Geometry.b1340.half 2 false=Geometry.b1943 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1943
  · have he : Geometry.b1340.half 2 true=Geometry.b1944 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1944

theorem bound1339 : BoxMajorant Geometry.b1339 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1339.Widths)
  · have he : Geometry.b1339.half 2 false=Geometry.b1941 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1941
  · have he : Geometry.b1339.half 2 true=Geometry.b1942 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1942

theorem bound1338 : BoxMajorant Geometry.b1338 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1338.Widths)
  · have he : Geometry.b1338.half 2 false=Geometry.b1939 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1939
  · have he : Geometry.b1338.half 2 true=Geometry.b1940 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1940

theorem bound1337 : BoxMajorant Geometry.b1337 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1337.Widths)
  · have he : Geometry.b1337.half 2 false=Geometry.b1937 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1937
  · have he : Geometry.b1337.half 2 true=Geometry.b1938 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1938

theorem bound958 : BoxMajorant Geometry.b958 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b958.Widths)
  · have he : Geometry.b958.half 1 false=Geometry.b1339 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1339
  · have he : Geometry.b958.half 1 true=Geometry.b1340 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1340

theorem bound957 : BoxMajorant Geometry.b957 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b957.Widths)
  · have he : Geometry.b957.half 1 false=Geometry.b1337 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1337
  · have he : Geometry.b957.half 1 true=Geometry.b1338 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1338

theorem bound663 : BoxMajorant Geometry.b663 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b663.Widths)
  · have he : Geometry.b663.half 0 false=Geometry.b957 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound957
  · have he : Geometry.b663.half 0 true=Geometry.b958 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound958

end N7.Kernel.Cover
