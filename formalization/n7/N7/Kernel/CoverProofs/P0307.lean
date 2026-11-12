import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.PositiveGroups.G0303
import N7.Kernel.PositiveGroups.G0326
import N7.Kernel.PositiveGroups.G0327
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4084 : BoxMajorant Geometry.b4084 := by
  exact PositiveLeaves.L924.bound

theorem bound4083 : BoxMajorant Geometry.b4083 := by
  exact PositiveLeaves.L925.bound

theorem bound3684 : BoxMajorant Geometry.b3684 := by
  exact PositiveLeaves.L923.bound

theorem bound3683 : BoxMajorant Geometry.b3683 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3683.Widths)
  · have he : Geometry.b3683.half 2 false=Geometry.b4083 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4083
  · have he : Geometry.b3683.half 2 true=Geometry.b4084 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4084

theorem bound3418 : BoxMajorant Geometry.b3418 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3418.Widths)
  · have he : Geometry.b3418.half 1 false=Geometry.b3683 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3683
  · have he : Geometry.b3418.half 1 true=Geometry.b3684 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3684

theorem bound3417 : BoxMajorant Geometry.b3417 := by
  exact PositiveLeaves.L926.bound

theorem bound3095 : BoxMajorant Geometry.b3095 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3095.Widths)
  · have he : Geometry.b3095.half 0 false=Geometry.b3417 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3417
  · have he : Geometry.b3095.half 0 true=Geometry.b3418 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3418

end N7.Kernel.Cover
