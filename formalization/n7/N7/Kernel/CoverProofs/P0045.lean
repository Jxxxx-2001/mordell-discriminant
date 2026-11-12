import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.PositiveGroups.G0027
import N7.Kernel.PositiveGroups.G0048
import N7.Kernel.PositiveGroups.G0075
import N7.Kernel.PositiveGroups.G0149
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2528 : BoxMajorant Geometry.b2528 := by
  exact PositiveLeaves.L2407.bound

theorem bound2527 : BoxMajorant Geometry.b2527 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2527 2 (by decide +kernel) x hx hd ho).elim

theorem bound2170 : BoxMajorant Geometry.b2170 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2170.Widths)
  · have he : Geometry.b2170.half 1 false=Geometry.b2527 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2527
  · have he : Geometry.b2170.half 1 true=Geometry.b2528 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2528

theorem bound2169 : BoxMajorant Geometry.b2169 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2169 2 (by decide +kernel) x hx hd ho).elim

theorem bound1536 : BoxMajorant Geometry.b1536 := by
  exact PositiveLeaves.L2406.bound

theorem bound1535 : BoxMajorant Geometry.b1535 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1535.Widths)
  · have he : Geometry.b1535.half 0 false=Geometry.b2169 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2169
  · have he : Geometry.b1535.half 0 true=Geometry.b2170 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2170

theorem bound1092 : BoxMajorant Geometry.b1092 := by
  exact PositiveLeaves.L2405.bound

theorem bound1091 : BoxMajorant Geometry.b1091 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1091.Widths)
  · have he : Geometry.b1091.half 2 false=Geometry.b1535 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1535
  · have he : Geometry.b1091.half 2 true=Geometry.b1536 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1536

theorem bound792 : BoxMajorant Geometry.b792 := by
  exact PositiveLeaves.L2404.bound

theorem bound791 : BoxMajorant Geometry.b791 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b791.Widths)
  · have he : Geometry.b791.half 1 false=Geometry.b1091 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1091
  · have he : Geometry.b791.half 1 true=Geometry.b1092 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1092

theorem bound510 : BoxMajorant Geometry.b510 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b510.Widths)
  · have he : Geometry.b510.half 0 false=Geometry.b791 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound791
  · have he : Geometry.b510.half 0 true=Geometry.b792 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound792

end N7.Kernel.Cover
