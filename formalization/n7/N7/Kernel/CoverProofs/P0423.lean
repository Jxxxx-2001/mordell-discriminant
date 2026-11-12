import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverGeometry.G0092
import N7.Kernel.PositiveGroups.G0497
import N7.Kernel.PositiveGroups.G0498
import N7.Kernel.PositiveGroups.G0502
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5904 : BoxMajorant Geometry.b5904 := by
  exact PositiveLeaves.L382.bound

theorem bound5903 : BoxMajorant Geometry.b5903 := by
  exact PositiveLeaves.L383.bound

theorem bound5902 : BoxMajorant Geometry.b5902 := by
  exact PositiveLeaves.L384.bound

theorem bound5901 : BoxMajorant Geometry.b5901 := by
  exact PositiveLeaves.L385.bound

theorem bound5858 : BoxMajorant Geometry.b5858 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5858.Widths)
  · have he : Geometry.b5858.half 2 false=Geometry.b5903 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5903
  · have he : Geometry.b5858.half 2 true=Geometry.b5904 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5904

theorem bound5857 : BoxMajorant Geometry.b5857 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5857.Widths)
  · have he : Geometry.b5857.half 2 false=Geometry.b5901 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5901
  · have he : Geometry.b5857.half 2 true=Geometry.b5902 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5902

theorem bound5823 : BoxMajorant Geometry.b5823 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5823.Widths)
  · have he : Geometry.b5823.half 1 false=Geometry.b5857 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5857
  · have he : Geometry.b5823.half 1 true=Geometry.b5858 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5858

end N7.Kernel.Cover
