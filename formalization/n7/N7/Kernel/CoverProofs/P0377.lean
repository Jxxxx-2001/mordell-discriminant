import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0434
import N7.Kernel.PositiveGroups.G0436
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5204 : BoxMajorant Geometry.b5204 := by
  exact PositiveLeaves.L1710.bound

theorem bound5203 : BoxMajorant Geometry.b5203 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5203 2 (by decide +kernel) x hx hd ho).elim

theorem bound4944 : BoxMajorant Geometry.b4944 := by
  exact PositiveLeaves.L1709.bound

theorem bound4943 : BoxMajorant Geometry.b4943 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4943.Widths)
  · have he : Geometry.b4943.half 0 false=Geometry.b5203 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5203
  · have he : Geometry.b4943.half 0 true=Geometry.b5204 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5204

theorem bound4596 : BoxMajorant Geometry.b4596 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4596.Widths)
  · have he : Geometry.b4596.half 2 false=Geometry.b4943 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4943
  · have he : Geometry.b4596.half 2 true=Geometry.b4944 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4944

end N7.Kernel.Cover
