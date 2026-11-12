import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.PositiveGroups.G0075
import N7.Kernel.PositiveGroups.G0149
import N7.Kernel.PositiveGroups.G0150
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2878 : BoxMajorant Geometry.b2878 := by
  exact PositiveLeaves.L2419.bound

theorem bound2877 : BoxMajorant Geometry.b2877 := by
  exact PositiveLeaves.L2420.bound

theorem bound2524 : BoxMajorant Geometry.b2524 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2524.Widths)
  · have he : Geometry.b2524.half 2 false=Geometry.b2877 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2877
  · have he : Geometry.b2524.half 2 true=Geometry.b2878 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2878

theorem bound2523 : BoxMajorant Geometry.b2523 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2523 0 (by decide +kernel) x hx hd ho).elim

theorem bound2166 : BoxMajorant Geometry.b2166 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2166 0 (by decide +kernel) x hx hd ho).elim

theorem bound2165 : BoxMajorant Geometry.b2165 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2165.Widths)
  · have he : Geometry.b2165.half 1 false=Geometry.b2523 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2523
  · have he : Geometry.b2165.half 1 true=Geometry.b2524 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2524

theorem bound1532 : BoxMajorant Geometry.b1532 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1532.Widths)
  · have he : Geometry.b1532.half 0 false=Geometry.b2165 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2165
  · have he : Geometry.b1532.half 0 true=Geometry.b2166 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2166

theorem bound1531 : BoxMajorant Geometry.b1531 := by
  exact PositiveLeaves.L2422.bound

theorem bound1088 : BoxMajorant Geometry.b1088 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1088.Widths)
  · have he : Geometry.b1088.half 2 false=Geometry.b1531 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1531
  · have he : Geometry.b1088.half 2 true=Geometry.b1532 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1532

theorem bound1087 : BoxMajorant Geometry.b1087 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1087 0 (by decide +kernel) x hx hd ho).elim

theorem bound787 : BoxMajorant Geometry.b787 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b787.Widths)
  · have he : Geometry.b787.half 1 false=Geometry.b1087 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1087
  · have he : Geometry.b787.half 1 true=Geometry.b1088 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1088

end N7.Kernel.Cover
