import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.PositiveGroups.G0086
import N7.Kernel.PositiveGroups.G0087
import N7.Kernel.PositiveGroups.G0122
import N7.Kernel.PositiveGroups.G0123
import N7.Kernel.PositiveGroups.G0124
import N7.Kernel.PositiveGroups.G0160
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2714 : BoxMajorant Geometry.b2714 := by
  exact PositiveLeaves.L866.bound

theorem bound2713 : BoxMajorant Geometry.b2713 := by
  exact PositiveLeaves.L867.bound

theorem bound2356 : BoxMajorant Geometry.b2356 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2356.Widths)
  · have he : Geometry.b2356.half 1 false=Geometry.b2713 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2713
  · have he : Geometry.b2356.half 1 true=Geometry.b2714 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2714

theorem bound2355 : BoxMajorant Geometry.b2355 := by
  exact PositiveLeaves.L868.bound

theorem bound2354 : BoxMajorant Geometry.b2354 := by
  exact PositiveLeaves.L873.bound

theorem bound2353 : BoxMajorant Geometry.b2353 := by
  exact PositiveLeaves.L874.bound

theorem bound1812 : BoxMajorant Geometry.b1812 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1812.Widths)
  · have he : Geometry.b1812.half 0 false=Geometry.b2355 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2355
  · have he : Geometry.b1812.half 0 true=Geometry.b2356 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2356

theorem bound1811 : BoxMajorant Geometry.b1811 := by
  exact PositiveLeaves.L869.bound

theorem bound1810 : BoxMajorant Geometry.b1810 := by
  exact PositiveLeaves.L870.bound

theorem bound1809 : BoxMajorant Geometry.b1809 := by
  exact PositiveLeaves.L871.bound

theorem bound1808 : BoxMajorant Geometry.b1808 := by
  exact PositiveLeaves.L872.bound

theorem bound1807 : BoxMajorant Geometry.b1807 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1807.Widths)
  · have he : Geometry.b1807.half 0 false=Geometry.b2353 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2353
  · have he : Geometry.b1807.half 0 true=Geometry.b2354 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2354

theorem bound1806 : BoxMajorant Geometry.b1806 := by
  exact PositiveLeaves.L875.bound

theorem bound1805 : BoxMajorant Geometry.b1805 := by
  exact PositiveLeaves.L876.bound

theorem bound1260 : BoxMajorant Geometry.b1260 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1260.Widths)
  · have he : Geometry.b1260.half 2 false=Geometry.b1811 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1811
  · have he : Geometry.b1260.half 2 true=Geometry.b1812 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1812

theorem bound1259 : BoxMajorant Geometry.b1259 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1259.Widths)
  · have he : Geometry.b1259.half 2 false=Geometry.b1809 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1809
  · have he : Geometry.b1259.half 2 true=Geometry.b1810 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1810

theorem bound1258 : BoxMajorant Geometry.b1258 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1258.Widths)
  · have he : Geometry.b1258.half 2 false=Geometry.b1807 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1807
  · have he : Geometry.b1258.half 2 true=Geometry.b1808 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1808

theorem bound1257 : BoxMajorant Geometry.b1257 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1257.Widths)
  · have he : Geometry.b1257.half 2 false=Geometry.b1805 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1805
  · have he : Geometry.b1257.half 2 true=Geometry.b1806 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1806

theorem bound910 : BoxMajorant Geometry.b910 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b910.Widths)
  · have he : Geometry.b910.half 1 false=Geometry.b1259 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1259
  · have he : Geometry.b910.half 1 true=Geometry.b1260 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1260

theorem bound909 : BoxMajorant Geometry.b909 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b909.Widths)
  · have he : Geometry.b909.half 1 false=Geometry.b1257 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1257
  · have he : Geometry.b909.half 1 true=Geometry.b1258 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1258

theorem bound624 : BoxMajorant Geometry.b624 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b624.Widths)
  · have he : Geometry.b624.half 0 false=Geometry.b909 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound909
  · have he : Geometry.b624.half 0 true=Geometry.b910 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound910

end N7.Kernel.Cover
