import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.PositiveGroups.G0128
import N7.Kernel.PositiveGroups.G0168
import N7.Kernel.PositiveGroups.G0169
import N7.Kernel.PositiveGroups.G0213
import N7.Kernel.PositiveGroups.G0214
import N7.Kernel.PositiveGroups.G0252
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2676 : BoxMajorant Geometry.b2676 := by
  exact PositiveLeaves.L1033.bound

theorem bound2675 : BoxMajorant Geometry.b2675 := by
  exact PositiveLeaves.L1034.bound

theorem bound2324 : BoxMajorant Geometry.b2324 := by
  exact PositiveLeaves.L1031.bound

theorem bound2323 : BoxMajorant Geometry.b2323 := by
  exact PositiveLeaves.L1032.bound

theorem bound2322 : BoxMajorant Geometry.b2322 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2322.Widths)
  · have he : Geometry.b2322.half 1 false=Geometry.b2675 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2675
  · have he : Geometry.b2322.half 1 true=Geometry.b2676 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2676

theorem bound2321 : BoxMajorant Geometry.b2321 := by
  exact PositiveLeaves.L1035.bound

theorem bound2320 : BoxMajorant Geometry.b2320 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2320 0 (by decide +kernel) x hx hd ho).elim

theorem bound2319 : BoxMajorant Geometry.b2319 := by
  exact PositiveLeaves.L1037.bound

theorem bound2318 : BoxMajorant Geometry.b2318 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2318 0 (by decide +kernel) x hx hd ho).elim

theorem bound2317 : BoxMajorant Geometry.b2317 := by
  exact PositiveLeaves.L1039.bound

theorem bound2316 : BoxMajorant Geometry.b2316 := by
  exact PositiveLeaves.L1040.bound

theorem bound2315 : BoxMajorant Geometry.b2315 := by
  exact PositiveLeaves.L1041.bound

theorem bound2314 : BoxMajorant Geometry.b2314 := by
  exact PositiveLeaves.L1042.bound

theorem bound2313 : BoxMajorant Geometry.b2313 := by
  exact PositiveLeaves.L1043.bound

theorem bound1772 : BoxMajorant Geometry.b1772 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1772.Widths)
  · have he : Geometry.b1772.half 0 false=Geometry.b2323 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2323
  · have he : Geometry.b1772.half 0 true=Geometry.b2324 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2324

theorem bound1771 : BoxMajorant Geometry.b1771 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1771.Widths)
  · have he : Geometry.b1771.half 0 false=Geometry.b2321 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2321
  · have he : Geometry.b1771.half 0 true=Geometry.b2322 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2322

theorem bound1770 : BoxMajorant Geometry.b1770 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1770.Widths)
  · have he : Geometry.b1770.half 0 false=Geometry.b2319 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2319
  · have he : Geometry.b1770.half 0 true=Geometry.b2320 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2320

theorem bound1769 : BoxMajorant Geometry.b1769 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1769.Widths)
  · have he : Geometry.b1769.half 0 false=Geometry.b2317 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2317
  · have he : Geometry.b1769.half 0 true=Geometry.b2318 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2318

theorem bound1768 : BoxMajorant Geometry.b1768 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1768.Widths)
  · have he : Geometry.b1768.half 0 false=Geometry.b2315 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2315
  · have he : Geometry.b1768.half 0 true=Geometry.b2316 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2316

theorem bound1767 : BoxMajorant Geometry.b1767 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1767.Widths)
  · have he : Geometry.b1767.half 0 false=Geometry.b2313 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2313
  · have he : Geometry.b1767.half 0 true=Geometry.b2314 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2314

theorem bound1766 : BoxMajorant Geometry.b1766 := by
  exact PositiveLeaves.L1044.bound

theorem bound1765 : BoxMajorant Geometry.b1765 := by
  exact PositiveLeaves.L1045.bound

theorem bound1240 : BoxMajorant Geometry.b1240 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1240.Widths)
  · have he : Geometry.b1240.half 2 false=Geometry.b1771 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1771
  · have he : Geometry.b1240.half 2 true=Geometry.b1772 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1772

theorem bound1239 : BoxMajorant Geometry.b1239 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1239.Widths)
  · have he : Geometry.b1239.half 2 false=Geometry.b1769 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1769
  · have he : Geometry.b1239.half 2 true=Geometry.b1770 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1770

theorem bound1238 : BoxMajorant Geometry.b1238 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1238.Widths)
  · have he : Geometry.b1238.half 2 false=Geometry.b1767 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1767
  · have he : Geometry.b1238.half 2 true=Geometry.b1768 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1768

theorem bound1237 : BoxMajorant Geometry.b1237 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1237.Widths)
  · have he : Geometry.b1237.half 2 false=Geometry.b1765 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1765
  · have he : Geometry.b1237.half 2 true=Geometry.b1766 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1766

theorem bound900 : BoxMajorant Geometry.b900 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b900.Widths)
  · have he : Geometry.b900.half 1 false=Geometry.b1239 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1239
  · have he : Geometry.b900.half 1 true=Geometry.b1240 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1240

theorem bound899 : BoxMajorant Geometry.b899 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b899.Widths)
  · have he : Geometry.b899.half 1 false=Geometry.b1237 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1237
  · have he : Geometry.b899.half 1 true=Geometry.b1238 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1238

theorem bound617 : BoxMajorant Geometry.b617 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b617.Widths)
  · have he : Geometry.b617.half 0 false=Geometry.b899 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound899
  · have he : Geometry.b617.half 0 true=Geometry.b900 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound900

end N7.Kernel.Cover
