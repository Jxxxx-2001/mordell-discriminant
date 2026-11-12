import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.PositiveGroups.G0404
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4864 : BoxMajorant Geometry.b4864 := by
  exact PositiveLeaves.L1974.bound

theorem bound4863 : BoxMajorant Geometry.b4863 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4863 2 (by decide +kernel) x hx hd ho).elim

theorem bound4548 : BoxMajorant Geometry.b4548 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4548.Widths)
  · have he : Geometry.b4548.half 2 false=Geometry.b4863 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4863
  · have he : Geometry.b4548.half 2 true=Geometry.b4864 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4864

end N7.Kernel.Cover
