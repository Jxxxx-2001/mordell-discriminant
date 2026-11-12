import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.PositiveGroups.G0186
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3804 : BoxMajorant Geometry.b3804 := by
  exact PositiveLeaves.L2516.bound

theorem bound3803 : BoxMajorant Geometry.b3803 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3803 2 (by decide +kernel) x hx hd ho).elim

theorem bound3506 : BoxMajorant Geometry.b3506 := by
  exact PositiveLeaves.L2515.bound

theorem bound3505 : BoxMajorant Geometry.b3505 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3505.Widths)
  · have he : Geometry.b3505.half 2 false=Geometry.b3803 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3803
  · have he : Geometry.b3505.half 2 true=Geometry.b3804 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3804

theorem bound3218 : BoxMajorant Geometry.b3218 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3218.Widths)
  · have he : Geometry.b3218.half 1 false=Geometry.b3505 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3505
  · have he : Geometry.b3218.half 1 true=Geometry.b3506 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3506

theorem bound3217 : BoxMajorant Geometry.b3217 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3217 2 (by decide +kernel) x hx hd ho).elim

theorem bound2852 : BoxMajorant Geometry.b2852 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2852.Widths)
  · have he : Geometry.b2852.half 0 false=Geometry.b3217 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3217
  · have he : Geometry.b2852.half 0 true=Geometry.b3218 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3218

end N7.Kernel.Cover
