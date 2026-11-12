import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.PositiveGroups.G0341
import N7.Kernel.PositiveGroups.G0373
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4300 : BoxMajorant Geometry.b4300 := by
  exact PositiveLeaves.L1812.bound

theorem bound4299 : BoxMajorant Geometry.b4299 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4299 2 (by decide +kernel) x hx hd ho).elim

theorem bound3946 : BoxMajorant Geometry.b3946 := by
  exact PositiveLeaves.L1811.bound

theorem bound3945 : BoxMajorant Geometry.b3945 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3945.Widths)
  · have he : Geometry.b3945.half 0 false=Geometry.b4299 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4299
  · have he : Geometry.b3945.half 0 true=Geometry.b4300 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4300

theorem bound3594 : BoxMajorant Geometry.b3594 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3594.Widths)
  · have he : Geometry.b3594.half 2 false=Geometry.b3945 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3945
  · have he : Geometry.b3594.half 2 true=Geometry.b3946 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3946

end N7.Kernel.Cover
