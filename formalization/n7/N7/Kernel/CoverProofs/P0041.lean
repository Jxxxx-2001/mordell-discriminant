import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.PositiveGroups.G0073
import N7.Kernel.PositiveGroups.G0074
import N7.Kernel.PositiveGroups.G0108
import N7.Kernel.PositiveGroups.G0109
import N7.Kernel.PositiveGroups.G0148
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2876 : BoxMajorant Geometry.b2876 := by
  exact PositiveLeaves.L2441.bound

theorem bound2875 : BoxMajorant Geometry.b2875 := by
  exact PositiveLeaves.L2442.bound

theorem bound2874 : BoxMajorant Geometry.b2874 := by
  exact PositiveLeaves.L2444.bound

theorem bound2873 : BoxMajorant Geometry.b2873 := by
  exact PositiveLeaves.L2445.bound

theorem bound2520 : BoxMajorant Geometry.b2520 := by
  exact PositiveLeaves.L2440.bound

theorem bound2519 : BoxMajorant Geometry.b2519 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2519.Widths)
  · have he : Geometry.b2519.half 2 false=Geometry.b2875 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2875
  · have he : Geometry.b2519.half 2 true=Geometry.b2876 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2876

theorem bound2518 : BoxMajorant Geometry.b2518 := by
  exact PositiveLeaves.L2443.bound

theorem bound2517 : BoxMajorant Geometry.b2517 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2517.Widths)
  · have he : Geometry.b2517.half 2 false=Geometry.b2873 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2873
  · have he : Geometry.b2517.half 2 true=Geometry.b2874 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2874

theorem bound2162 : BoxMajorant Geometry.b2162 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2162.Widths)
  · have he : Geometry.b2162.half 1 false=Geometry.b2519 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2519
  · have he : Geometry.b2162.half 1 true=Geometry.b2520 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2520

theorem bound2161 : BoxMajorant Geometry.b2161 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2161.Widths)
  · have he : Geometry.b2161.half 1 false=Geometry.b2517 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2517
  · have he : Geometry.b2161.half 1 true=Geometry.b2518 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2518

theorem bound1528 : BoxMajorant Geometry.b1528 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1528.Widths)
  · have he : Geometry.b1528.half 0 false=Geometry.b2161 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2161
  · have he : Geometry.b1528.half 0 true=Geometry.b2162 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2162

theorem bound1527 : BoxMajorant Geometry.b1527 := by
  exact PositiveLeaves.L2446.bound

theorem bound1526 : BoxMajorant Geometry.b1526 := by
  exact PositiveLeaves.L2447.bound

theorem bound1525 : BoxMajorant Geometry.b1525 := by
  exact PositiveLeaves.L2448.bound

theorem bound1524 : BoxMajorant Geometry.b1524 := by
  exact PositiveLeaves.L2449.bound

theorem bound1523 : BoxMajorant Geometry.b1523 := by
  exact PositiveLeaves.L2450.bound

theorem bound1082 : BoxMajorant Geometry.b1082 := by
  exact PositiveLeaves.L2439.bound

theorem bound1081 : BoxMajorant Geometry.b1081 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1081.Widths)
  · have he : Geometry.b1081.half 2 false=Geometry.b1527 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1527
  · have he : Geometry.b1081.half 2 true=Geometry.b1528 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1528

theorem bound1080 : BoxMajorant Geometry.b1080 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1080.Widths)
  · have he : Geometry.b1080.half 2 false=Geometry.b1525 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1525
  · have he : Geometry.b1080.half 2 true=Geometry.b1526 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1526

theorem bound1079 : BoxMajorant Geometry.b1079 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1079.Widths)
  · have he : Geometry.b1079.half 2 false=Geometry.b1523 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1523
  · have he : Geometry.b1079.half 2 true=Geometry.b1524 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1524

theorem bound782 : BoxMajorant Geometry.b782 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b782.Widths)
  · have he : Geometry.b782.half 1 false=Geometry.b1081 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1081
  · have he : Geometry.b782.half 1 true=Geometry.b1082 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1082

theorem bound781 : BoxMajorant Geometry.b781 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b781.Widths)
  · have he : Geometry.b781.half 1 false=Geometry.b1079 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1079
  · have he : Geometry.b781.half 1 true=Geometry.b1080 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1080

theorem bound502 : BoxMajorant Geometry.b502 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b502.Widths)
  · have he : Geometry.b502.half 0 false=Geometry.b781 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound781
  · have he : Geometry.b502.half 0 true=Geometry.b782 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound782

end N7.Kernel.Cover
