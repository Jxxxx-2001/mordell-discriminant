import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.PositiveGroups.G0002
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound174 : BoxMajorant Geometry.b174 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b174 1 (by decide +kernel) x hx hd ho).elim

theorem bound173 : BoxMajorant Geometry.b173 := by
  exact PositiveLeaves.L526.bound

theorem bound102 : BoxMajorant Geometry.b102 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b102.Widths)
  · have he : Geometry.b102.half 2 false=Geometry.b173 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound173
  · have he : Geometry.b102.half 2 true=Geometry.b174 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound174

theorem bound101 : BoxMajorant Geometry.b101 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b101 0 (by decide +kernel) x hx hd ho).elim

theorem bound55 : BoxMajorant Geometry.b55 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b55.Widths)
  · have he : Geometry.b55.half 1 false=Geometry.b101 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound101
  · have he : Geometry.b55.half 1 true=Geometry.b102 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound102

end N7.Kernel.Cover
