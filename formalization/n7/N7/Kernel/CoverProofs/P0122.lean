import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0054
import N7.Kernel.PositiveGroups.G0055
import N7.Kernel.PositiveGroups.G0084
import N7.Kernel.PositiveGroups.G0085
import N7.Kernel.PositiveGroups.G0086
import N7.Kernel.PositiveGroups.G0122
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3114 : BoxMajorant Geometry.b3114 := by
  exact PositiveLeaves.L851.bound

theorem bound3113 : BoxMajorant Geometry.b3113 := by
  exact PositiveLeaves.L852.bound

theorem bound2718 : BoxMajorant Geometry.b2718 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2718.Widths)
  · have he : Geometry.b2718.half 2 false=Geometry.b3113 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3113
  · have he : Geometry.b2718.half 2 true=Geometry.b3114 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3114

theorem bound2717 : BoxMajorant Geometry.b2717 := by
  exact PositiveLeaves.L853.bound

theorem bound2716 : BoxMajorant Geometry.b2716 := by
  exact PositiveLeaves.L858.bound

theorem bound2715 : BoxMajorant Geometry.b2715 := by
  exact PositiveLeaves.L859.bound

theorem bound2362 : BoxMajorant Geometry.b2362 := by
  exact PositiveLeaves.L850.bound

theorem bound2361 : BoxMajorant Geometry.b2361 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2361.Widths)
  · have he : Geometry.b2361.half 1 false=Geometry.b2717 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2717
  · have he : Geometry.b2361.half 1 true=Geometry.b2718 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2718

theorem bound2360 : BoxMajorant Geometry.b2360 := by
  exact PositiveLeaves.L855.bound

theorem bound2359 : BoxMajorant Geometry.b2359 := by
  exact PositiveLeaves.L856.bound

theorem bound2358 : BoxMajorant Geometry.b2358 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2358.Widths)
  · have he : Geometry.b2358.half 1 false=Geometry.b2715 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2715
  · have he : Geometry.b2358.half 1 true=Geometry.b2716 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2716

theorem bound2357 : BoxMajorant Geometry.b2357 := by
  exact PositiveLeaves.L860.bound

theorem bound1822 : BoxMajorant Geometry.b1822 := by
  exact PositiveLeaves.L848.bound

theorem bound1821 : BoxMajorant Geometry.b1821 := by
  exact PositiveLeaves.L849.bound

theorem bound1820 : BoxMajorant Geometry.b1820 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1820.Widths)
  · have he : Geometry.b1820.half 0 false=Geometry.b2361 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2361
  · have he : Geometry.b1820.half 0 true=Geometry.b2362 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2362

theorem bound1819 : BoxMajorant Geometry.b1819 := by
  exact PositiveLeaves.L854.bound

theorem bound1818 : BoxMajorant Geometry.b1818 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1818.Widths)
  · have he : Geometry.b1818.half 0 false=Geometry.b2359 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2359
  · have he : Geometry.b1818.half 0 true=Geometry.b2360 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2360

theorem bound1817 : BoxMajorant Geometry.b1817 := by
  exact PositiveLeaves.L857.bound

theorem bound1816 : BoxMajorant Geometry.b1816 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1816.Widths)
  · have he : Geometry.b1816.half 0 false=Geometry.b2357 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2357
  · have he : Geometry.b1816.half 0 true=Geometry.b2358 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2358

theorem bound1815 : BoxMajorant Geometry.b1815 := by
  exact PositiveLeaves.L861.bound

theorem bound1266 : BoxMajorant Geometry.b1266 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1266.Widths)
  · have he : Geometry.b1266.half 2 false=Geometry.b1821 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1821
  · have he : Geometry.b1266.half 2 true=Geometry.b1822 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1822

theorem bound1265 : BoxMajorant Geometry.b1265 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1265.Widths)
  · have he : Geometry.b1265.half 2 false=Geometry.b1819 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1819
  · have he : Geometry.b1265.half 2 true=Geometry.b1820 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1820

theorem bound1264 : BoxMajorant Geometry.b1264 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1264.Widths)
  · have he : Geometry.b1264.half 2 false=Geometry.b1817 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1817
  · have he : Geometry.b1264.half 2 true=Geometry.b1818 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1818

theorem bound1263 : BoxMajorant Geometry.b1263 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1263.Widths)
  · have he : Geometry.b1263.half 2 false=Geometry.b1815 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1815
  · have he : Geometry.b1263.half 2 true=Geometry.b1816 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1816

theorem bound914 : BoxMajorant Geometry.b914 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b914.Widths)
  · have he : Geometry.b914.half 1 false=Geometry.b1265 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1265
  · have he : Geometry.b914.half 1 true=Geometry.b1266 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1266

theorem bound913 : BoxMajorant Geometry.b913 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b913.Widths)
  · have he : Geometry.b913.half 1 false=Geometry.b1263 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1263
  · have he : Geometry.b913.half 1 true=Geometry.b1264 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1264

theorem bound626 : BoxMajorant Geometry.b626 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b626.Widths)
  · have he : Geometry.b626.half 0 false=Geometry.b913 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound913
  · have he : Geometry.b626.half 0 true=Geometry.b914 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound914

end N7.Kernel.Cover
