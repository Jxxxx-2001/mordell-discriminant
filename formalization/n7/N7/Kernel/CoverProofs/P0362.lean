import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.PositiveGroups.G0421
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5178 : BoxMajorant Geometry.b5178 := by
  exact PositiveLeaves.L1976.bound

theorem bound5177 : BoxMajorant Geometry.b5177 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5177 2 (by decide +kernel) x hx hd ho).elim

theorem bound4862 : BoxMajorant Geometry.b4862 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4862.Widths)
  · have he : Geometry.b4862.half 0 false=Geometry.b5177 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5177
  · have he : Geometry.b4862.half 0 true=Geometry.b5178 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5178

theorem bound4861 : BoxMajorant Geometry.b4861 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4861 2 (by decide +kernel) x hx hd ho).elim

theorem bound4547 : BoxMajorant Geometry.b4547 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4547.Widths)
  · have he : Geometry.b4547.half 2 false=Geometry.b4861 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4861
  · have he : Geometry.b4547.half 2 true=Geometry.b4862 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4862

end N7.Kernel.Cover
