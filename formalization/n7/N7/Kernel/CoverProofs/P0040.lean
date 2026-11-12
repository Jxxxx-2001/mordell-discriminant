import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.PositiveGroups.G0025
import N7.Kernel.PositiveGroups.G0073
import N7.Kernel.PositiveGroups.G0074
import N7.Kernel.PositiveGroups.G0109
import N7.Kernel.PositiveGroups.G0110
import N7.Kernel.PositiveGroups.G0148
import N7.Kernel.PositiveGroups.G0149
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2872 : BoxMajorant Geometry.b2872 := by
  exact PositiveLeaves.L2454.bound

theorem bound2871 : BoxMajorant Geometry.b2871 := by
  exact PositiveLeaves.L2455.bound

theorem bound2870 : BoxMajorant Geometry.b2870 := by
  exact PositiveLeaves.L2456.bound

theorem bound2869 : BoxMajorant Geometry.b2869 := by
  exact PositiveLeaves.L2457.bound

theorem bound2516 : BoxMajorant Geometry.b2516 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2516.Widths)
  · have he : Geometry.b2516.half 2 false=Geometry.b2871 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2871
  · have he : Geometry.b2516.half 2 true=Geometry.b2872 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2872

theorem bound2515 : BoxMajorant Geometry.b2515 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2515.Widths)
  · have he : Geometry.b2515.half 2 false=Geometry.b2869 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2869
  · have he : Geometry.b2515.half 2 true=Geometry.b2870 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2870

theorem bound2160 : BoxMajorant Geometry.b2160 := by
  exact PositiveLeaves.L2453.bound

theorem bound2159 : BoxMajorant Geometry.b2159 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2159.Widths)
  · have he : Geometry.b2159.half 1 false=Geometry.b2515 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2515
  · have he : Geometry.b2159.half 1 true=Geometry.b2516 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2516

theorem bound1522 : BoxMajorant Geometry.b1522 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1522.Widths)
  · have he : Geometry.b1522.half 0 false=Geometry.b2159 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2159
  · have he : Geometry.b1522.half 0 true=Geometry.b2160 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2160

theorem bound1521 : BoxMajorant Geometry.b1521 := by
  exact PositiveLeaves.L2458.bound

theorem bound1520 : BoxMajorant Geometry.b1520 := by
  exact PositiveLeaves.L2459.bound

theorem bound1519 : BoxMajorant Geometry.b1519 := by
  exact PositiveLeaves.L2460.bound

theorem bound1078 : BoxMajorant Geometry.b1078 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1078.Widths)
  · have he : Geometry.b1078.half 2 false=Geometry.b1521 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1521
  · have he : Geometry.b1078.half 2 true=Geometry.b1522 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1522

theorem bound1077 : BoxMajorant Geometry.b1077 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1077.Widths)
  · have he : Geometry.b1077.half 2 false=Geometry.b1519 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1519
  · have he : Geometry.b1077.half 2 true=Geometry.b1520 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1520

theorem bound780 : BoxMajorant Geometry.b780 := by
  exact PositiveLeaves.L2452.bound

theorem bound779 : BoxMajorant Geometry.b779 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b779.Widths)
  · have he : Geometry.b779.half 1 false=Geometry.b1077 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1077
  · have he : Geometry.b779.half 1 true=Geometry.b1078 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1078

theorem bound500 : BoxMajorant Geometry.b500 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b500.Widths)
  · have he : Geometry.b500.half 0 false=Geometry.b779 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound779
  · have he : Geometry.b500.half 0 true=Geometry.b780 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound780

end N7.Kernel.Cover
