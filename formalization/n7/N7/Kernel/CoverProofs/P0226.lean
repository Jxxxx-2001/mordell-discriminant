import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.PositiveGroups.G0292
import N7.Kernel.PositiveGroups.G0293
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3294 : BoxMajorant Geometry.b3294 := by
  exact PositiveLeaves.L1939.bound

theorem bound3293 : BoxMajorant Geometry.b3293 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3293 2 (by decide +kernel) x hx hd ho).elim

theorem bound2958 : BoxMajorant Geometry.b2958 := by
  exact PositiveLeaves.L1938.bound

theorem bound2957 : BoxMajorant Geometry.b2957 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2957.Widths)
  · have he : Geometry.b2957.half 0 false=Geometry.b3293 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3293
  · have he : Geometry.b2957.half 0 true=Geometry.b3294 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3294

theorem bound2592 : BoxMajorant Geometry.b2592 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2592.Widths)
  · have he : Geometry.b2592.half 2 false=Geometry.b2957 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2957
  · have he : Geometry.b2592.half 2 true=Geometry.b2958 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2958

end N7.Kernel.Cover
