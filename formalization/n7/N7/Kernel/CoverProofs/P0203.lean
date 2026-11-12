import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.PositiveGroups.G0320
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3802 : BoxMajorant Geometry.b3802 := by
  exact PositiveLeaves.L2579.bound

theorem bound3801 : BoxMajorant Geometry.b3801 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3801 2 (by decide +kernel) x hx hd ho).elim

theorem bound3504 : BoxMajorant Geometry.b3504 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3504.Widths)
  · have he : Geometry.b3504.half 2 false=Geometry.b3801 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3801
  · have he : Geometry.b3504.half 2 true=Geometry.b3802 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3802

theorem bound3503 : BoxMajorant Geometry.b3503 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3503 0 (by decide +kernel) x hx hd ho).elim

theorem bound3216 : BoxMajorant Geometry.b3216 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3216 0 (by decide +kernel) x hx hd ho).elim

theorem bound3215 : BoxMajorant Geometry.b3215 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3215.Widths)
  · have he : Geometry.b3215.half 1 false=Geometry.b3503 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3503
  · have he : Geometry.b3215.half 1 true=Geometry.b3504 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3504

theorem bound2837 : BoxMajorant Geometry.b2837 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2837.Widths)
  · have he : Geometry.b2837.half 0 false=Geometry.b3215 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3215
  · have he : Geometry.b2837.half 0 true=Geometry.b3216 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3216

end N7.Kernel.Cover
