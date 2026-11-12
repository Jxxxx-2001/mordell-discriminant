import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.PositiveGroups.G0078
import N7.Kernel.PositiveGroups.G0115
import N7.Kernel.PositiveGroups.G0116
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3402 : BoxMajorant Geometry.b3402 := by
  exact PositiveLeaves.L1209.bound

theorem bound3401 : BoxMajorant Geometry.b3401 := by
  exact PositiveLeaves.L1210.bound

theorem bound3068 : BoxMajorant Geometry.b3068 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3068.Widths)
  · have he : Geometry.b3068.half 0 false=Geometry.b3401 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3401
  · have he : Geometry.b3068.half 0 true=Geometry.b3402 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3402

theorem bound3067 : BoxMajorant Geometry.b3067 := by
  exact PositiveLeaves.L1211.bound

theorem bound2664 : BoxMajorant Geometry.b2664 := by
  exact PositiveLeaves.L1208.bound

theorem bound2663 : BoxMajorant Geometry.b2663 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2663.Widths)
  · have he : Geometry.b2663.half 2 false=Geometry.b3067 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3067
  · have he : Geometry.b2663.half 2 true=Geometry.b3068 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3068

theorem bound2292 : BoxMajorant Geometry.b2292 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2292.Widths)
  · have he : Geometry.b2292.half 1 false=Geometry.b2663 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2663
  · have he : Geometry.b2292.half 1 true=Geometry.b2664 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2664

theorem bound2291 : BoxMajorant Geometry.b2291 := by
  exact PositiveLeaves.L1212.bound

theorem bound1670 : BoxMajorant Geometry.b1670 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1670.Widths)
  · have he : Geometry.b1670.half 0 false=Geometry.b2291 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2291
  · have he : Geometry.b1670.half 0 true=Geometry.b2292 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2292

end N7.Kernel.Cover
