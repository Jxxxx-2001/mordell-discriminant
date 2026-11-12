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
theorem bound3306 : BoxMajorant Geometry.b3306 := by
  exact PositiveLeaves.L1883.bound

theorem bound3305 : BoxMajorant Geometry.b3305 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3305 2 (by decide +kernel) x hx hd ho).elim

theorem bound2970 : BoxMajorant Geometry.b2970 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2970.Widths)
  · have he : Geometry.b2970.half 0 false=Geometry.b3305 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3305
  · have he : Geometry.b2970.half 0 true=Geometry.b3306 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3306

theorem bound2969 : BoxMajorant Geometry.b2969 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2969 2 (by decide +kernel) x hx hd ho).elim

theorem bound2598 : BoxMajorant Geometry.b2598 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2598.Widths)
  · have he : Geometry.b2598.half 2 false=Geometry.b2969 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2969
  · have he : Geometry.b2598.half 2 true=Geometry.b2970 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2970

end N7.Kernel.Cover
