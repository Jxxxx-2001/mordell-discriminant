import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.PositiveGroups.G0037
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1010 : BoxMajorant Geometry.b1010 := by
  exact PositiveLeaves.L93.bound

theorem bound1009 : BoxMajorant Geometry.b1009 := by
  exact PositiveLeaves.L94.bound

theorem bound708 : BoxMajorant Geometry.b708 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b708.Widths)
  · have he : Geometry.b708.half 0 false=Geometry.b1009 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1009
  · have he : Geometry.b708.half 0 true=Geometry.b1010 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1010

end N7.Kernel.Cover
