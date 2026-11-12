import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.PositiveGroups.G0303
import N7.Kernel.PositiveGroups.G0304
import N7.Kernel.PositiveGroups.G0326
import N7.Kernel.PositiveGroups.G0327
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4082 : BoxMajorant Geometry.b4082 := by
  exact PositiveLeaves.L928.bound

theorem bound4081 : BoxMajorant Geometry.b4081 := by
  exact PositiveLeaves.L929.bound

theorem bound3682 : BoxMajorant Geometry.b3682 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3682.Widths)
  · have he : Geometry.b3682.half 2 false=Geometry.b4081 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4081
  · have he : Geometry.b3682.half 2 true=Geometry.b4082 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4082

theorem bound3681 : BoxMajorant Geometry.b3681 := by
  exact PositiveLeaves.L930.bound

theorem bound3680 : BoxMajorant Geometry.b3680 := by
  exact PositiveLeaves.L931.bound

theorem bound3679 : BoxMajorant Geometry.b3679 := by
  exact PositiveLeaves.L932.bound

theorem bound3416 : BoxMajorant Geometry.b3416 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3416.Widths)
  · have he : Geometry.b3416.half 1 false=Geometry.b3681 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3681
  · have he : Geometry.b3416.half 1 true=Geometry.b3682 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3682

theorem bound3415 : BoxMajorant Geometry.b3415 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3415.Widths)
  · have he : Geometry.b3415.half 1 false=Geometry.b3679 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3679
  · have he : Geometry.b3415.half 1 true=Geometry.b3680 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3680

theorem bound3093 : BoxMajorant Geometry.b3093 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3093.Widths)
  · have he : Geometry.b3093.half 0 false=Geometry.b3415 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3415
  · have he : Geometry.b3093.half 0 true=Geometry.b3416 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3416

end N7.Kernel.Cover
