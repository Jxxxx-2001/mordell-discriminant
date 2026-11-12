import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverGeometry.G0092
import N7.Kernel.PositiveGroups.G0502
import N7.Kernel.PositiveGroups.G0503
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5908 : BoxMajorant Geometry.b5908 := by
  exact PositiveLeaves.L378.bound

theorem bound5907 : BoxMajorant Geometry.b5907 := by
  exact PositiveLeaves.L379.bound

theorem bound5906 : BoxMajorant Geometry.b5906 := by
  exact PositiveLeaves.L380.bound

theorem bound5905 : BoxMajorant Geometry.b5905 := by
  exact PositiveLeaves.L381.bound

theorem bound5860 : BoxMajorant Geometry.b5860 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5860.Widths)
  · have he : Geometry.b5860.half 2 false=Geometry.b5907 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5907
  · have he : Geometry.b5860.half 2 true=Geometry.b5908 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5908

theorem bound5859 : BoxMajorant Geometry.b5859 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5859.Widths)
  · have he : Geometry.b5859.half 2 false=Geometry.b5905 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5905
  · have he : Geometry.b5859.half 2 true=Geometry.b5906 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5906

theorem bound5824 : BoxMajorant Geometry.b5824 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5824.Widths)
  · have he : Geometry.b5824.half 1 false=Geometry.b5859 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5859
  · have he : Geometry.b5824.half 1 true=Geometry.b5860 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5860

end N7.Kernel.Cover
