import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0417
import N7.Kernel.PositiveGroups.G0435
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5202 : BoxMajorant Geometry.b5202 := by
  exact PositiveLeaves.L1716.bound

theorem bound5201 : BoxMajorant Geometry.b5201 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5201 2 (by decide +kernel) x hx hd ho).elim

theorem bound4940 : BoxMajorant Geometry.b4940 := by
  exact PositiveLeaves.L1715.bound

theorem bound4939 : BoxMajorant Geometry.b4939 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4939.Widths)
  · have he : Geometry.b4939.half 0 false=Geometry.b5201 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5201
  · have he : Geometry.b4939.half 0 true=Geometry.b5202 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5202

theorem bound4594 : BoxMajorant Geometry.b4594 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4594.Widths)
  · have he : Geometry.b4594.half 2 false=Geometry.b4939 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4939
  · have he : Geometry.b4594.half 2 true=Geometry.b4940 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4940

end N7.Kernel.Cover
