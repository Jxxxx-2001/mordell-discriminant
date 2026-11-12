import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.PositiveGroups.G0294
import N7.Kernel.PositiveGroups.G0317
import N7.Kernel.PositiveGroups.G0318
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3838 : BoxMajorant Geometry.b3838 := by
  exact PositiveLeaves.L2124.bound

theorem bound3837 : BoxMajorant Geometry.b3837 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3837 2 (by decide +kernel) x hx hd ho).elim

theorem bound3532 : BoxMajorant Geometry.b3532 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3532.Widths)
  · have he : Geometry.b3532.half 2 false=Geometry.b3837 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3837
  · have he : Geometry.b3532.half 2 true=Geometry.b3838 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3838

theorem bound3531 : BoxMajorant Geometry.b3531 := by
  exact PositiveLeaves.L2126.bound

theorem bound3258 : BoxMajorant Geometry.b3258 := by
  exact PositiveLeaves.L2123.bound

theorem bound3257 : BoxMajorant Geometry.b3257 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3257.Widths)
  · have he : Geometry.b3257.half 1 false=Geometry.b3531 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3531
  · have he : Geometry.b3257.half 1 true=Geometry.b3532 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3532

theorem bound2932 : BoxMajorant Geometry.b2932 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2932.Widths)
  · have he : Geometry.b2932.half 0 false=Geometry.b3257 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3257
  · have he : Geometry.b2932.half 0 true=Geometry.b3258 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3258

end N7.Kernel.Cover
