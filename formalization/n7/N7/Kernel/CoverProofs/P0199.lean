import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.PositiveGroups.G0267
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3492 : BoxMajorant Geometry.b3492 := by
  exact PositiveLeaves.L2637.bound

theorem bound3491 : BoxMajorant Geometry.b3491 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3491 2 (by decide +kernel) x hx hd ho).elim

theorem bound3208 : BoxMajorant Geometry.b3208 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3208.Widths)
  · have he : Geometry.b3208.half 1 false=Geometry.b3491 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3491
  · have he : Geometry.b3208.half 1 true=Geometry.b3492 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3492

theorem bound3207 : BoxMajorant Geometry.b3207 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3207 2 (by decide +kernel) x hx hd ho).elim

theorem bound2832 : BoxMajorant Geometry.b2832 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2832.Widths)
  · have he : Geometry.b2832.half 0 false=Geometry.b3207 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3207
  · have he : Geometry.b2832.half 0 true=Geometry.b3208 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3208

end N7.Kernel.Cover
