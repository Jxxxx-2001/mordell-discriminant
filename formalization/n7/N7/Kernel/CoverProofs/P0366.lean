import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.PositiveGroups.G0423
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5174 : BoxMajorant Geometry.b5174 := by
  exact PositiveLeaves.L2041.bound

theorem bound5173 : BoxMajorant Geometry.b5173 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5173 2 (by decide +kernel) x hx hd ho).elim

theorem bound4844 : BoxMajorant Geometry.b4844 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4844.Widths)
  · have he : Geometry.b4844.half 0 false=Geometry.b5173 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5173
  · have he : Geometry.b4844.half 0 true=Geometry.b5174 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5174

theorem bound4843 : BoxMajorant Geometry.b4843 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4843 2 (by decide +kernel) x hx hd ho).elim

theorem bound4535 : BoxMajorant Geometry.b4535 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4535.Widths)
  · have he : Geometry.b4535.half 2 false=Geometry.b4843 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4843
  · have he : Geometry.b4535.half 2 true=Geometry.b4844 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4844

end N7.Kernel.Cover
