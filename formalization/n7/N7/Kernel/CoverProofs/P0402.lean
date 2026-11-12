import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.PositiveGroups.G0446
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5098 : BoxMajorant Geometry.b5098 := by
  exact PositiveLeaves.L196.bound

theorem bound5097 : BoxMajorant Geometry.b5097 := by
  exact PositiveLeaves.L197.bound

theorem bound4710 : BoxMajorant Geometry.b4710 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4710.Widths)
  · have he : Geometry.b4710.half 2 false=Geometry.b5097 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5097
  · have he : Geometry.b4710.half 2 true=Geometry.b5098 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5098

end N7.Kernel.Cover
