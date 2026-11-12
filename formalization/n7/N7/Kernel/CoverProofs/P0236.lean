import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.PositiveGroups.G0290
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3304 : BoxMajorant Geometry.b3304 := by
  exact PositiveLeaves.L1886.bound

theorem bound3303 : BoxMajorant Geometry.b3303 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3303 2 (by decide +kernel) x hx hd ho).elim

theorem bound2968 : BoxMajorant Geometry.b2968 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2968.Widths)
  · have he : Geometry.b2968.half 0 false=Geometry.b3303 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3303
  · have he : Geometry.b2968.half 0 true=Geometry.b3304 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3304

theorem bound2967 : BoxMajorant Geometry.b2967 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2967 2 (by decide +kernel) x hx hd ho).elim

theorem bound2597 : BoxMajorant Geometry.b2597 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2597.Widths)
  · have he : Geometry.b2597.half 2 false=Geometry.b2967 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2967
  · have he : Geometry.b2597.half 2 true=Geometry.b2968 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2968

end N7.Kernel.Cover
