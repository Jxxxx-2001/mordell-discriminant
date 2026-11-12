import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0399
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5212 : BoxMajorant Geometry.b5212 := by
  exact PositiveLeaves.L1671.bound

theorem bound5211 : BoxMajorant Geometry.b5211 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5211 2 (by decide +kernel) x hx hd ho).elim

theorem bound4963 : BoxMajorant Geometry.b4963 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4963.Widths)
  · have he : Geometry.b4963.half 0 false=Geometry.b5211 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5211
  · have he : Geometry.b4963.half 0 true=Geometry.b5212 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5212

end N7.Kernel.Cover
