import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0426
import N7.Kernel.PositiveGroups.G0441
import N7.Kernel.PositiveGroups.G0455
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5434 : BoxMajorant Geometry.b5434 := by
  exact PositiveLeaves.L2836.bound

theorem bound5433 : BoxMajorant Geometry.b5433 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5433 2 (by decide +kernel) x hx hd ho).elim

theorem bound5304 : BoxMajorant Geometry.b5304 := by
  exact PositiveLeaves.L2835.bound

theorem bound5303 : BoxMajorant Geometry.b5303 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5303.Widths)
  · have he : Geometry.b5303.half 2 false=Geometry.b5433 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5433
  · have he : Geometry.b5303.half 2 true=Geometry.b5434 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5434

theorem bound5122 : BoxMajorant Geometry.b5122 := by
  exact PositiveLeaves.L2834.bound

theorem bound5121 : BoxMajorant Geometry.b5121 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5121.Widths)
  · have he : Geometry.b5121.half 1 false=Geometry.b5303 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5303
  · have he : Geometry.b5121.half 1 true=Geometry.b5304 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5304

theorem bound4740 : BoxMajorant Geometry.b4740 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4740.Widths)
  · have he : Geometry.b4740.half 0 false=Geometry.b5121 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5121
  · have he : Geometry.b4740.half 0 true=Geometry.b5122 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5122

end N7.Kernel.Cover
