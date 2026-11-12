import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0416
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5196 : BoxMajorant Geometry.b5196 := by
  exact PositiveLeaves.L1724.bound

theorem bound5195 : BoxMajorant Geometry.b5195 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5195 2 (by decide +kernel) x hx hd ho).elim

theorem bound4934 : BoxMajorant Geometry.b4934 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4934.Widths)
  · have he : Geometry.b4934.half 0 false=Geometry.b5195 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5195
  · have he : Geometry.b4934.half 0 true=Geometry.b5196 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5196

theorem bound4933 : BoxMajorant Geometry.b4933 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4933 2 (by decide +kernel) x hx hd ho).elim

theorem bound4591 : BoxMajorant Geometry.b4591 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4591.Widths)
  · have he : Geometry.b4591.half 2 false=Geometry.b4933 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4933
  · have he : Geometry.b4591.half 2 true=Geometry.b4934 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4934

end N7.Kernel.Cover
