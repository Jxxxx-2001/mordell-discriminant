import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0428
import N7.Kernel.PositiveGroups.G0442
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5410 : BoxMajorant Geometry.b5410 := by
  exact PositiveLeaves.L2883.bound

theorem bound5409 : BoxMajorant Geometry.b5409 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5409 2 (by decide +kernel) x hx hd ho).elim

theorem bound5286 : BoxMajorant Geometry.b5286 := by
  exact PositiveLeaves.L2882.bound

theorem bound5285 : BoxMajorant Geometry.b5285 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5285.Widths)
  · have he : Geometry.b5285.half 2 false=Geometry.b5409 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5409
  · have he : Geometry.b5285.half 2 true=Geometry.b5410 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5410

theorem bound5109 : BoxMajorant Geometry.b5109 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5109.Widths)
  · have he : Geometry.b5109.half 1 false=Geometry.b5285 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5285
  · have he : Geometry.b5109.half 1 true=Geometry.b5286 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5286

end N7.Kernel.Cover
