import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverProofs.P0291
import N7.Kernel.CoverProofs.P0292
import N7.Kernel.CoverProofs.P0293
import N7.Kernel.CoverProofs.P0294
import N7.Kernel.CoverProofs.P0295
import N7.Kernel.CoverProofs.P0296
import N7.Kernel.CoverProofs.P0297
import N7.Kernel.PositiveGroups.G0166
import N7.Kernel.PositiveGroups.G0167
import N7.Kernel.PositiveGroups.G0213
import N7.Kernel.PositiveGroups.G0249
import N7.Kernel.PositiveGroups.G0251
import N7.Kernel.PositiveGroups.G0252
import N7.Kernel.PositiveGroups.G0281
import N7.Kernel.PositiveGroups.G0282
import N7.Kernel.PositiveGroups.G0283
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3082 : BoxMajorant Geometry.b3082 := by
  exact PositiveLeaves.L962.bound

theorem bound3081 : BoxMajorant Geometry.b3081 := by
  exact PositiveLeaves.L963.bound

theorem bound3080 : BoxMajorant Geometry.b3080 := by
  exact PositiveLeaves.L964.bound

theorem bound3079 : BoxMajorant Geometry.b3079 := by
  exact PositiveLeaves.L965.bound

theorem bound3076 : BoxMajorant Geometry.b3076 := by
  exact PositiveLeaves.L974.bound

theorem bound3074 : BoxMajorant Geometry.b3074 := by
  exact PositiveLeaves.L994.bound

theorem bound2685 : BoxMajorant Geometry.b2685 := by
  exact PositiveLeaves.L961.bound

theorem bound2684 : BoxMajorant Geometry.b2684 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2684.Widths)
  · have he : Geometry.b2684.half 2 false=Geometry.b3081 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3081
  · have he : Geometry.b2684.half 2 true=Geometry.b3082 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3082

theorem bound2683 : BoxMajorant Geometry.b2683 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2683.Widths)
  · have he : Geometry.b2683.half 2 false=Geometry.b3079 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3079
  · have he : Geometry.b2683.half 2 true=Geometry.b3080 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3080

theorem bound2682 : BoxMajorant Geometry.b2682 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2682.Widths)
  · have he : Geometry.b2682.half 2 false=Geometry.b3077 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3077
  · have he : Geometry.b2682.half 2 true=Geometry.b3078 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3078

theorem bound2681 : BoxMajorant Geometry.b2681 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2681.Widths)
  · have he : Geometry.b2681.half 2 false=Geometry.b3075 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3075
  · have he : Geometry.b2681.half 2 true=Geometry.b3076 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3076

theorem bound2680 : BoxMajorant Geometry.b2680 := by
  exact PositiveLeaves.L990.bound

theorem bound2679 : BoxMajorant Geometry.b2679 := by
  exact PositiveLeaves.L991.bound

theorem bound2678 : BoxMajorant Geometry.b2678 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2678.Widths)
  · have he : Geometry.b2678.half 2 false=Geometry.b3073 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3073
  · have he : Geometry.b2678.half 2 true=Geometry.b3074 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3074

theorem bound2677 : BoxMajorant Geometry.b2677 := by
  exact PositiveLeaves.L1028.bound

theorem bound2332 : BoxMajorant Geometry.b2332 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2332.Widths)
  · have he : Geometry.b2332.half 1 false=Geometry.b2687 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2687
  · have he : Geometry.b2332.half 1 true=Geometry.b2688 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2688

theorem bound2331 : BoxMajorant Geometry.b2331 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2331.Widths)
  · have he : Geometry.b2331.half 1 false=Geometry.b2685 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2685
  · have he : Geometry.b2331.half 1 true=Geometry.b2686 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2686

theorem bound2330 : BoxMajorant Geometry.b2330 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2330.Widths)
  · have he : Geometry.b2330.half 1 false=Geometry.b2683 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2683
  · have he : Geometry.b2330.half 1 true=Geometry.b2684 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2684

theorem bound2329 : BoxMajorant Geometry.b2329 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2329.Widths)
  · have he : Geometry.b2329.half 1 false=Geometry.b2681 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2681
  · have he : Geometry.b2329.half 1 true=Geometry.b2682 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2682

theorem bound2328 : BoxMajorant Geometry.b2328 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2328.Widths)
  · have he : Geometry.b2328.half 1 false=Geometry.b2679 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2679
  · have he : Geometry.b2328.half 1 true=Geometry.b2680 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2680

theorem bound2327 : BoxMajorant Geometry.b2327 := by
  exact PositiveLeaves.L992.bound

theorem bound2326 : BoxMajorant Geometry.b2326 := by
  exact PositiveLeaves.L993.bound

theorem bound2325 : BoxMajorant Geometry.b2325 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2325.Widths)
  · have he : Geometry.b2325.half 1 false=Geometry.b2677 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2677
  · have he : Geometry.b2325.half 1 true=Geometry.b2678 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2678

theorem bound1780 : BoxMajorant Geometry.b1780 := by
  exact PositiveLeaves.L951.bound

theorem bound1779 : BoxMajorant Geometry.b1779 := by
  exact PositiveLeaves.L952.bound

theorem bound1778 : BoxMajorant Geometry.b1778 := by
  exact PositiveLeaves.L953.bound

theorem bound1777 : BoxMajorant Geometry.b1777 := by
  exact PositiveLeaves.L954.bound

theorem bound1776 : BoxMajorant Geometry.b1776 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1776.Widths)
  · have he : Geometry.b1776.half 0 false=Geometry.b2331 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2331
  · have he : Geometry.b1776.half 0 true=Geometry.b2332 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2332

theorem bound1775 : BoxMajorant Geometry.b1775 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1775.Widths)
  · have he : Geometry.b1775.half 0 false=Geometry.b2329 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2329
  · have he : Geometry.b1775.half 0 true=Geometry.b2330 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2330

theorem bound1774 : BoxMajorant Geometry.b1774 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1774.Widths)
  · have he : Geometry.b1774.half 0 false=Geometry.b2327 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2327
  · have he : Geometry.b1774.half 0 true=Geometry.b2328 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2328

theorem bound1773 : BoxMajorant Geometry.b1773 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1773.Widths)
  · have he : Geometry.b1773.half 0 false=Geometry.b2325 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2325
  · have he : Geometry.b1773.half 0 true=Geometry.b2326 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2326

theorem bound1244 : BoxMajorant Geometry.b1244 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1244.Widths)
  · have he : Geometry.b1244.half 2 false=Geometry.b1779 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1779
  · have he : Geometry.b1244.half 2 true=Geometry.b1780 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1780

theorem bound1243 : BoxMajorant Geometry.b1243 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1243.Widths)
  · have he : Geometry.b1243.half 2 false=Geometry.b1777 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1777
  · have he : Geometry.b1243.half 2 true=Geometry.b1778 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1778

theorem bound1242 : BoxMajorant Geometry.b1242 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1242.Widths)
  · have he : Geometry.b1242.half 2 false=Geometry.b1775 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1775
  · have he : Geometry.b1242.half 2 true=Geometry.b1776 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1776

theorem bound1241 : BoxMajorant Geometry.b1241 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1241.Widths)
  · have he : Geometry.b1241.half 2 false=Geometry.b1773 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1773
  · have he : Geometry.b1241.half 2 true=Geometry.b1774 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1774

theorem bound902 : BoxMajorant Geometry.b902 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b902.Widths)
  · have he : Geometry.b902.half 1 false=Geometry.b1243 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1243
  · have he : Geometry.b902.half 1 true=Geometry.b1244 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1244

theorem bound901 : BoxMajorant Geometry.b901 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b901.Widths)
  · have he : Geometry.b901.half 1 false=Geometry.b1241 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1241
  · have he : Geometry.b901.half 1 true=Geometry.b1242 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1242

theorem bound619 : BoxMajorant Geometry.b619 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b619.Widths)
  · have he : Geometry.b619.half 0 false=Geometry.b901 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound901
  · have he : Geometry.b619.half 0 true=Geometry.b902 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound902

end N7.Kernel.Cover
