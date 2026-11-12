import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.PositiveGroups.G0064
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound990 : BoxMajorant Geometry.b990 := by
  exact PositiveLeaves.L499.bound

theorem bound989 : BoxMajorant Geometry.b989 := by
  exact PositiveLeaves.L500.bound

theorem bound693 : BoxMajorant Geometry.b693 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b693.Widths)
  · have he : Geometry.b693.half 0 false=Geometry.b989 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound989
  · have he : Geometry.b693.half 0 true=Geometry.b990 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound990

end N7.Kernel.Cover
