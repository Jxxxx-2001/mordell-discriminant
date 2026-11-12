import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.PositiveGroups.G0298
import N7.Kernel.PositiveGroups.G0323
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3764 : BoxMajorant Geometry.b3764 := by
  exact PositiveLeaves.L2729.bound

theorem bound3763 : BoxMajorant Geometry.b3763 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3763 2 (by decide +kernel) x hx hd ho).elim

theorem bound3474 : BoxMajorant Geometry.b3474 := by
  exact PositiveLeaves.L2728.bound

theorem bound3473 : BoxMajorant Geometry.b3473 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3473.Widths)
  · have he : Geometry.b3473.half 2 false=Geometry.b3763 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3763
  · have he : Geometry.b3473.half 2 true=Geometry.b3764 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3764

theorem bound3196 : BoxMajorant Geometry.b3196 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3196.Widths)
  · have he : Geometry.b3196.half 1 false=Geometry.b3473 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3473
  · have he : Geometry.b3196.half 1 true=Geometry.b3474 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3474

theorem bound3195 : BoxMajorant Geometry.b3195 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3195 2 (by decide +kernel) x hx hd ho).elim

theorem bound2809 : BoxMajorant Geometry.b2809 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2809.Widths)
  · have he : Geometry.b2809.half 0 false=Geometry.b3195 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3195
  · have he : Geometry.b2809.half 0 true=Geometry.b3196 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3196

end N7.Kernel.Cover
