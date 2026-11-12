import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.PositiveGroups.G0041
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound850 : BoxMajorant Geometry.b850 := by
  exact PositiveLeaves.L1357.bound

theorem bound849 : BoxMajorant Geometry.b849 := by
  exact PositiveLeaves.L1358.bound

theorem bound576 : BoxMajorant Geometry.b576 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b576.Widths)
  · have he : Geometry.b576.half 0 false=Geometry.b849 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound849
  · have he : Geometry.b576.half 0 true=Geometry.b850 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound850

end N7.Kernel.Cover
