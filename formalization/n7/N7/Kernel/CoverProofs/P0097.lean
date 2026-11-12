import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0171
import N7.Kernel.PositiveGroups.G0172
import N7.Kernel.PositiveGroups.G0215
import N7.Kernel.PositiveGroups.G0216
import N7.Kernel.PositiveGroups.G0252
import N7.Kernel.PositiveGroups.G0253
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3072 : BoxMajorant Geometry.b3072 := by
  exact PositiveLeaves.L1143.bound

theorem bound3071 : BoxMajorant Geometry.b3071 := by
  exact PositiveLeaves.L1144.bound

theorem bound2672 : BoxMajorant Geometry.b2672 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2672.Widths)
  · have he : Geometry.b2672.half 2 false=Geometry.b3071 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3071
  · have he : Geometry.b2672.half 2 true=Geometry.b3072 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3072

theorem bound2671 : BoxMajorant Geometry.b2671 := by
  exact PositiveLeaves.L1145.bound

theorem bound2670 : BoxMajorant Geometry.b2670 := by
  exact PositiveLeaves.L1147.bound

theorem bound2669 : BoxMajorant Geometry.b2669 := by
  exact PositiveLeaves.L1148.bound

theorem bound2300 : BoxMajorant Geometry.b2300 := by
  exact PositiveLeaves.L1142.bound

theorem bound2299 : BoxMajorant Geometry.b2299 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2299.Widths)
  · have he : Geometry.b2299.half 1 false=Geometry.b2671 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2671
  · have he : Geometry.b2299.half 1 true=Geometry.b2672 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2672

theorem bound2298 : BoxMajorant Geometry.b2298 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2298.Widths)
  · have he : Geometry.b2298.half 1 false=Geometry.b2669 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2669
  · have he : Geometry.b2298.half 1 true=Geometry.b2670 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2670

theorem bound2297 : BoxMajorant Geometry.b2297 := by
  exact PositiveLeaves.L1149.bound

theorem bound1702 : BoxMajorant Geometry.b1702 := by
  exact PositiveLeaves.L1141.bound

theorem bound1701 : BoxMajorant Geometry.b1701 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1701.Widths)
  · have he : Geometry.b1701.half 0 false=Geometry.b2299 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2299
  · have he : Geometry.b1701.half 0 true=Geometry.b2300 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2300

theorem bound1700 : BoxMajorant Geometry.b1700 := by
  exact PositiveLeaves.L1146.bound

theorem bound1699 : BoxMajorant Geometry.b1699 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1699.Widths)
  · have he : Geometry.b1699.half 0 false=Geometry.b2297 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2297
  · have he : Geometry.b1699.half 0 true=Geometry.b2298 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2298

theorem bound1198 : BoxMajorant Geometry.b1198 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1198.Widths)
  · have he : Geometry.b1198.half 2 false=Geometry.b1701 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1701
  · have he : Geometry.b1198.half 2 true=Geometry.b1702 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1702

theorem bound1197 : BoxMajorant Geometry.b1197 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1197.Widths)
  · have he : Geometry.b1197.half 2 false=Geometry.b1699 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1699
  · have he : Geometry.b1197.half 2 true=Geometry.b1700 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1700

theorem bound871 : BoxMajorant Geometry.b871 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b871.Widths)
  · have he : Geometry.b871.half 1 false=Geometry.b1197 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1197
  · have he : Geometry.b871.half 1 true=Geometry.b1198 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1198

end N7.Kernel.Cover
