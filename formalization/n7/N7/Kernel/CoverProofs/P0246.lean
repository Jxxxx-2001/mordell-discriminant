import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.PositiveGroups.G0316
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3298 : BoxMajorant Geometry.b3298 := by
  exact PositiveLeaves.L1929.bound

theorem bound3297 : BoxMajorant Geometry.b3297 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3297 2 (by decide +kernel) x hx hd ho).elim

theorem bound2962 : BoxMajorant Geometry.b2962 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2962.Widths)
  · have he : Geometry.b2962.half 0 false=Geometry.b3297 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3297
  · have he : Geometry.b2962.half 0 true=Geometry.b3298 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3298

end N7.Kernel.Cover
