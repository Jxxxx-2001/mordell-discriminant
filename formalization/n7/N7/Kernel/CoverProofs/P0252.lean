import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.PositiveGroups.G0341
import N7.Kernel.PositiveGroups.G0372
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4298 : BoxMajorant Geometry.b4298 := by
  exact PositiveLeaves.L1815.bound

theorem bound4297 : BoxMajorant Geometry.b4297 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4297 2 (by decide +kernel) x hx hd ho).elim

theorem bound3944 : BoxMajorant Geometry.b3944 := by
  exact PositiveLeaves.L1814.bound

theorem bound3943 : BoxMajorant Geometry.b3943 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3943.Widths)
  · have he : Geometry.b3943.half 0 false=Geometry.b4297 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4297
  · have he : Geometry.b3943.half 0 true=Geometry.b4298 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4298

theorem bound3593 : BoxMajorant Geometry.b3593 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3593.Widths)
  · have he : Geometry.b3593.half 2 false=Geometry.b3943 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3943
  · have he : Geometry.b3593.half 2 true=Geometry.b3944 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3944

end N7.Kernel.Cover
