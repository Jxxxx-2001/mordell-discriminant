import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.PositiveGroups.G0169
import N7.Kernel.PositiveGroups.G0170
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1706 : BoxMajorant Geometry.b1706 := by
  exact PositiveLeaves.L1137.bound

theorem bound1705 : BoxMajorant Geometry.b1705 := by
  exact PositiveLeaves.L1138.bound

theorem bound1704 : BoxMajorant Geometry.b1704 := by
  exact PositiveLeaves.L1139.bound

theorem bound1703 : BoxMajorant Geometry.b1703 := by
  exact PositiveLeaves.L1140.bound

theorem bound1200 : BoxMajorant Geometry.b1200 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1200.Widths)
  · have he : Geometry.b1200.half 2 false=Geometry.b1705 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1705
  · have he : Geometry.b1200.half 2 true=Geometry.b1706 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1706

theorem bound1199 : BoxMajorant Geometry.b1199 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1199.Widths)
  · have he : Geometry.b1199.half 2 false=Geometry.b1703 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1703
  · have he : Geometry.b1199.half 2 true=Geometry.b1704 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1704

theorem bound872 : BoxMajorant Geometry.b872 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b872.Widths)
  · have he : Geometry.b872.half 1 false=Geometry.b1199 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1199
  · have he : Geometry.b872.half 1 true=Geometry.b1200 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1200

end N7.Kernel.Cover
