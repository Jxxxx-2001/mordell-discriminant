import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverProofs.P0283
import N7.Kernel.CoverProofs.P0284
import N7.Kernel.CoverProofs.P0285
import N7.Kernel.CoverProofs.P0286
import N7.Kernel.PositiveGroups.G0067
import N7.Kernel.PositiveGroups.G0102
import N7.Kernel.PositiveGroups.G0178
import N7.Kernel.PositiveGroups.G0179
import N7.Kernel.PositiveGroups.G0221
import N7.Kernel.PositiveGroups.G0222
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3392 : BoxMajorant Geometry.b3392 := by
  exact PositiveLeaves.L1369.bound

theorem bound3391 : BoxMajorant Geometry.b3391 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3391.Widths)
  · have he : Geometry.b3391.half 1 false=Geometry.b3657 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3657
  · have he : Geometry.b3391.half 1 true=Geometry.b3658 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3658

theorem bound3390 : BoxMajorant Geometry.b3390 := by
  exact PositiveLeaves.L1375.bound

theorem bound3389 : BoxMajorant Geometry.b3389 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3389.Widths)
  · have he : Geometry.b3389.half 1 false=Geometry.b3655 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3655
  · have he : Geometry.b3389.half 1 true=Geometry.b3656 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3656

theorem bound3388 : BoxMajorant Geometry.b3388 := by
  exact PositiveLeaves.L1383.bound

theorem bound3387 : BoxMajorant Geometry.b3387 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3387 2 (by decide +kernel) x hx hd ho).elim

theorem bound3386 : BoxMajorant Geometry.b3386 := by
  exact PositiveLeaves.L1386.bound

theorem bound3385 : BoxMajorant Geometry.b3385 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3385 2 (by decide +kernel) x hx hd ho).elim

theorem bound3056 : BoxMajorant Geometry.b3056 := by
  exact PositiveLeaves.L1368.bound

theorem bound3055 : BoxMajorant Geometry.b3055 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3055.Widths)
  · have he : Geometry.b3055.half 0 false=Geometry.b3391 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3391
  · have he : Geometry.b3055.half 0 true=Geometry.b3392 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3392

theorem bound3054 : BoxMajorant Geometry.b3054 := by
  exact PositiveLeaves.L1374.bound

theorem bound3053 : BoxMajorant Geometry.b3053 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3053.Widths)
  · have he : Geometry.b3053.half 0 false=Geometry.b3389 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3389
  · have he : Geometry.b3053.half 0 true=Geometry.b3390 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3390

theorem bound3052 : BoxMajorant Geometry.b3052 := by
  exact PositiveLeaves.L1382.bound

theorem bound3051 : BoxMajorant Geometry.b3051 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3051.Widths)
  · have he : Geometry.b3051.half 0 false=Geometry.b3387 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3387
  · have he : Geometry.b3051.half 0 true=Geometry.b3388 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3388

theorem bound3050 : BoxMajorant Geometry.b3050 := by
  exact PositiveLeaves.L1385.bound

theorem bound3049 : BoxMajorant Geometry.b3049 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3049.Widths)
  · have he : Geometry.b3049.half 0 false=Geometry.b3385 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3385
  · have he : Geometry.b3049.half 0 true=Geometry.b3386 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3386

theorem bound2646 : BoxMajorant Geometry.b2646 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2646.Widths)
  · have he : Geometry.b2646.half 2 false=Geometry.b3055 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3055
  · have he : Geometry.b2646.half 2 true=Geometry.b3056 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3056

theorem bound2645 : BoxMajorant Geometry.b2645 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2645.Widths)
  · have he : Geometry.b2645.half 2 false=Geometry.b3053 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3053
  · have he : Geometry.b2645.half 2 true=Geometry.b3054 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3054

theorem bound2644 : BoxMajorant Geometry.b2644 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2644.Widths)
  · have he : Geometry.b2644.half 2 false=Geometry.b3051 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3051
  · have he : Geometry.b2644.half 2 true=Geometry.b3052 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3052

theorem bound2643 : BoxMajorant Geometry.b2643 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2643.Widths)
  · have he : Geometry.b2643.half 2 false=Geometry.b3049 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3049
  · have he : Geometry.b2643.half 2 true=Geometry.b3050 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3050

theorem bound2274 : BoxMajorant Geometry.b2274 := by
  exact PositiveLeaves.L1367.bound

theorem bound2273 : BoxMajorant Geometry.b2273 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2273.Widths)
  · have he : Geometry.b2273.half 1 false=Geometry.b2645 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2645
  · have he : Geometry.b2273.half 1 true=Geometry.b2646 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2646

theorem bound2272 : BoxMajorant Geometry.b2272 := by
  exact PositiveLeaves.L1381.bound

theorem bound2271 : BoxMajorant Geometry.b2271 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2271.Widths)
  · have he : Geometry.b2271.half 1 false=Geometry.b2643 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2643
  · have he : Geometry.b2271.half 1 true=Geometry.b2644 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2644

theorem bound1658 : BoxMajorant Geometry.b1658 := by
  exact PositiveLeaves.L1366.bound

theorem bound1657 : BoxMajorant Geometry.b1657 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1657.Widths)
  · have he : Geometry.b1657.half 0 false=Geometry.b2273 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2273
  · have he : Geometry.b1657.half 0 true=Geometry.b2274 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2274

theorem bound1656 : BoxMajorant Geometry.b1656 := by
  exact PositiveLeaves.L1380.bound

theorem bound1655 : BoxMajorant Geometry.b1655 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1655.Widths)
  · have he : Geometry.b1655.half 0 false=Geometry.b2271 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2271
  · have he : Geometry.b1655.half 0 true=Geometry.b2272 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2272

theorem bound1166 : BoxMajorant Geometry.b1166 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1166.Widths)
  · have he : Geometry.b1166.half 2 false=Geometry.b1657 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1657
  · have he : Geometry.b1166.half 2 true=Geometry.b1658 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1658

theorem bound1165 : BoxMajorant Geometry.b1165 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1165.Widths)
  · have he : Geometry.b1165.half 2 false=Geometry.b1655 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1655
  · have he : Geometry.b1165.half 2 true=Geometry.b1656 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1656

theorem bound847 : BoxMajorant Geometry.b847 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b847.Widths)
  · have he : Geometry.b847.half 1 false=Geometry.b1165 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1165
  · have he : Geometry.b847.half 1 true=Geometry.b1166 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1166

end N7.Kernel.Cover
