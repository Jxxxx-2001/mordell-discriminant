import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0125
import N7.Kernel.PositiveGroups.G0126
import N7.Kernel.PositiveGroups.G0163
import N7.Kernel.PositiveGroups.G0164
import N7.Kernel.PositiveGroups.G0210
import N7.Kernel.PositiveGroups.G0247
import N7.Kernel.PositiveGroups.G0248
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3112 : BoxMajorant Geometry.b3112 := by
  exact PositiveLeaves.L884.bound

theorem bound3111 : BoxMajorant Geometry.b3111 := by
  exact PositiveLeaves.L885.bound

theorem bound2712 : BoxMajorant Geometry.b2712 := by
  exact PositiveLeaves.L879.bound

theorem bound2711 : BoxMajorant Geometry.b2711 := by
  exact PositiveLeaves.L880.bound

theorem bound2710 : BoxMajorant Geometry.b2710 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2710.Widths)
  · have he : Geometry.b2710.half 2 false=Geometry.b3111 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3111
  · have he : Geometry.b2710.half 2 true=Geometry.b3112 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3112

theorem bound2709 : BoxMajorant Geometry.b2709 := by
  exact PositiveLeaves.L886.bound

theorem bound2708 : BoxMajorant Geometry.b2708 := by
  exact PositiveLeaves.L891.bound

theorem bound2707 : BoxMajorant Geometry.b2707 := by
  exact PositiveLeaves.L892.bound

theorem bound2352 : BoxMajorant Geometry.b2352 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2352.Widths)
  · have he : Geometry.b2352.half 1 false=Geometry.b2711 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2711
  · have he : Geometry.b2352.half 1 true=Geometry.b2712 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2712

theorem bound2351 : BoxMajorant Geometry.b2351 := by
  exact PositiveLeaves.L881.bound

theorem bound2350 : BoxMajorant Geometry.b2350 := by
  exact PositiveLeaves.L883.bound

theorem bound2349 : BoxMajorant Geometry.b2349 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2349.Widths)
  · have he : Geometry.b2349.half 1 false=Geometry.b2709 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2709
  · have he : Geometry.b2349.half 1 true=Geometry.b2710 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2710

theorem bound2348 : BoxMajorant Geometry.b2348 := by
  exact PositiveLeaves.L888.bound

theorem bound2347 : BoxMajorant Geometry.b2347 := by
  exact PositiveLeaves.L889.bound

theorem bound2346 : BoxMajorant Geometry.b2346 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2346.Widths)
  · have he : Geometry.b2346.half 1 false=Geometry.b2707 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2707
  · have he : Geometry.b2346.half 1 true=Geometry.b2708 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2708

theorem bound2345 : BoxMajorant Geometry.b2345 := by
  exact PositiveLeaves.L893.bound

theorem bound1804 : BoxMajorant Geometry.b1804 := by
  exact PositiveLeaves.L878.bound

theorem bound1803 : BoxMajorant Geometry.b1803 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1803.Widths)
  · have he : Geometry.b1803.half 0 false=Geometry.b2351 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2351
  · have he : Geometry.b1803.half 0 true=Geometry.b2352 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2352

theorem bound1802 : BoxMajorant Geometry.b1802 := by
  exact PositiveLeaves.L882.bound

theorem bound1801 : BoxMajorant Geometry.b1801 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1801.Widths)
  · have he : Geometry.b1801.half 0 false=Geometry.b2349 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2349
  · have he : Geometry.b1801.half 0 true=Geometry.b2350 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2350

theorem bound1800 : BoxMajorant Geometry.b1800 := by
  exact PositiveLeaves.L887.bound

theorem bound1799 : BoxMajorant Geometry.b1799 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1799.Widths)
  · have he : Geometry.b1799.half 0 false=Geometry.b2347 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2347
  · have he : Geometry.b1799.half 0 true=Geometry.b2348 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2348

theorem bound1798 : BoxMajorant Geometry.b1798 := by
  exact PositiveLeaves.L890.bound

theorem bound1797 : BoxMajorant Geometry.b1797 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1797.Widths)
  · have he : Geometry.b1797.half 0 false=Geometry.b2345 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2345
  · have he : Geometry.b1797.half 0 true=Geometry.b2346 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2346

theorem bound1256 : BoxMajorant Geometry.b1256 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1256.Widths)
  · have he : Geometry.b1256.half 2 false=Geometry.b1803 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1803
  · have he : Geometry.b1256.half 2 true=Geometry.b1804 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1804

theorem bound1255 : BoxMajorant Geometry.b1255 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1255.Widths)
  · have he : Geometry.b1255.half 2 false=Geometry.b1801 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1801
  · have he : Geometry.b1255.half 2 true=Geometry.b1802 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1802

theorem bound1254 : BoxMajorant Geometry.b1254 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1254.Widths)
  · have he : Geometry.b1254.half 2 false=Geometry.b1799 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1799
  · have he : Geometry.b1254.half 2 true=Geometry.b1800 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1800

theorem bound1253 : BoxMajorant Geometry.b1253 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1253.Widths)
  · have he : Geometry.b1253.half 2 false=Geometry.b1797 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1797
  · have he : Geometry.b1253.half 2 true=Geometry.b1798 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1798

theorem bound908 : BoxMajorant Geometry.b908 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b908.Widths)
  · have he : Geometry.b908.half 1 false=Geometry.b1255 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1255
  · have he : Geometry.b908.half 1 true=Geometry.b1256 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1256

theorem bound907 : BoxMajorant Geometry.b907 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b907.Widths)
  · have he : Geometry.b907.half 1 false=Geometry.b1253 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1253
  · have he : Geometry.b907.half 1 true=Geometry.b1254 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1254

theorem bound622 : BoxMajorant Geometry.b622 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b622.Widths)
  · have he : Geometry.b622.half 0 false=Geometry.b907 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound907
  · have he : Geometry.b622.half 0 true=Geometry.b908 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound908

end N7.Kernel.Cover
