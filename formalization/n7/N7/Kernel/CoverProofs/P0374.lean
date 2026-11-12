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
theorem bound5200 : BoxMajorant Geometry.b5200 := by
  exact PositiveLeaves.L1719.bound

theorem bound5199 : BoxMajorant Geometry.b5199 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5199 2 (by decide +kernel) x hx hd ho).elim

theorem bound4938 : BoxMajorant Geometry.b4938 := by
  exact PositiveLeaves.L1718.bound

theorem bound4937 : BoxMajorant Geometry.b4937 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4937.Widths)
  · have he : Geometry.b4937.half 0 false=Geometry.b5199 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5199
  · have he : Geometry.b4937.half 0 true=Geometry.b5200 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5200

theorem bound4593 : BoxMajorant Geometry.b4593 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4593.Widths)
  · have he : Geometry.b4593.half 2 false=Geometry.b4937 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4937
  · have he : Geometry.b4593.half 2 true=Geometry.b4938 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4938

end N7.Kernel.Cover
