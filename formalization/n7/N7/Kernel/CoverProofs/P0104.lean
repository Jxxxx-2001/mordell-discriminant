import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.PositiveGroups.G0091
import N7.Kernel.PositiveGroups.G0092
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1726 : BoxMajorant Geometry.b1726 := by
  exact PositiveLeaves.L1112.bound

theorem bound1725 : BoxMajorant Geometry.b1725 := by
  exact PositiveLeaves.L1113.bound

theorem bound1724 : BoxMajorant Geometry.b1724 := by
  exact PositiveLeaves.L1114.bound

theorem bound1723 : BoxMajorant Geometry.b1723 := by
  exact PositiveLeaves.L1115.bound

theorem bound1212 : BoxMajorant Geometry.b1212 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1212.Widths)
  · have he : Geometry.b1212.half 2 false=Geometry.b1725 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1725
  · have he : Geometry.b1212.half 2 true=Geometry.b1726 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1726

theorem bound1211 : BoxMajorant Geometry.b1211 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1211.Widths)
  · have he : Geometry.b1211.half 2 false=Geometry.b1723 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1723
  · have he : Geometry.b1211.half 2 true=Geometry.b1724 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1724

theorem bound878 : BoxMajorant Geometry.b878 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b878.Widths)
  · have he : Geometry.b878.half 1 false=Geometry.b1211 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1211
  · have he : Geometry.b878.half 1 true=Geometry.b1212 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1212

end N7.Kernel.Cover
