import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.PositiveGroups.G0407
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4766 : BoxMajorant Geometry.b4766 := by
  exact PositiveLeaves.L2766.bound

theorem bound4765 : BoxMajorant Geometry.b4765 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4765 2 (by decide +kernel) x hx hd ho).elim

theorem bound4477 : BoxMajorant Geometry.b4477 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4477.Widths)
  · have he : Geometry.b4477.half 2 false=Geometry.b4765 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4765
  · have he : Geometry.b4477.half 2 true=Geometry.b4766 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4766

end N7.Kernel.Cover
