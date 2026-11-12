import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.PositiveGroups.G0458
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5082 : BoxMajorant Geometry.b5082 := by
  exact PositiveLeaves.L250.bound

theorem bound5081 : BoxMajorant Geometry.b5081 := by
  exact PositiveLeaves.L251.bound

theorem bound4700 : BoxMajorant Geometry.b4700 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4700.Widths)
  · have he : Geometry.b4700.half 2 false=Geometry.b5081 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5081
  · have he : Geometry.b4700.half 2 true=Geometry.b5082 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5082

end N7.Kernel.Cover
