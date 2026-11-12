import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.PositiveGroups.G0058
import N7.Kernel.PositiveGroups.G0090
import N7.Kernel.PositiveGroups.G0091
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1722 : BoxMajorant Geometry.b1722 := by
  exact PositiveLeaves.L1116.bound

theorem bound1721 : BoxMajorant Geometry.b1721 := by
  exact PositiveLeaves.L1117.bound

theorem bound1210 : BoxMajorant Geometry.b1210 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1210.Widths)
  · have he : Geometry.b1210.half 2 false=Geometry.b1721 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1721
  · have he : Geometry.b1210.half 2 true=Geometry.b1722 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1722

theorem bound1209 : BoxMajorant Geometry.b1209 := by
  exact PositiveLeaves.L1118.bound

theorem bound877 : BoxMajorant Geometry.b877 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b877.Widths)
  · have he : Geometry.b877.half 1 false=Geometry.b1209 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1209
  · have he : Geometry.b877.half 1 true=Geometry.b1210 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1210

end N7.Kernel.Cover
