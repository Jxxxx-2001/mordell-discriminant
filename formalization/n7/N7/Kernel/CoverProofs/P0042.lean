import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.PositiveGroups.G0045
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1084 : BoxMajorant Geometry.b1084 := by
  exact PositiveLeaves.L2436.bound

theorem bound1083 : BoxMajorant Geometry.b1083 := by
  exact PositiveLeaves.L2437.bound

theorem bound784 : BoxMajorant Geometry.b784 := by
  exact PositiveLeaves.L2435.bound

theorem bound783 : BoxMajorant Geometry.b783 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b783.Widths)
  · have he : Geometry.b783.half 1 false=Geometry.b1083 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1083
  · have he : Geometry.b783.half 1 true=Geometry.b1084 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1084

theorem bound504 : BoxMajorant Geometry.b504 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b504.Widths)
  · have he : Geometry.b504.half 0 false=Geometry.b783 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound783
  · have he : Geometry.b504.half 0 true=Geometry.b784 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound784

end N7.Kernel.Cover
