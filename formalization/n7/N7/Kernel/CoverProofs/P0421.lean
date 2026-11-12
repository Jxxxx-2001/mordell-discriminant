import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverGeometry.G0092
import N7.Kernel.PositiveGroups.G0504
import N7.Kernel.PositiveGroups.G0506
import N7.Kernel.PositiveGroups.G0507
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5896 : BoxMajorant Geometry.b5896 := by
  exact PositiveLeaves.L396.bound

theorem bound5895 : BoxMajorant Geometry.b5895 := by
  exact PositiveLeaves.L397.bound

theorem bound5894 : BoxMajorant Geometry.b5894 := by
  exact PositiveLeaves.L398.bound

theorem bound5893 : BoxMajorant Geometry.b5893 := by
  exact PositiveLeaves.L399.bound

theorem bound5854 : BoxMajorant Geometry.b5854 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5854.Widths)
  · have he : Geometry.b5854.half 2 false=Geometry.b5895 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5895
  · have he : Geometry.b5854.half 2 true=Geometry.b5896 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5896

theorem bound5853 : BoxMajorant Geometry.b5853 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5853.Widths)
  · have he : Geometry.b5853.half 2 false=Geometry.b5893 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5893
  · have he : Geometry.b5853.half 2 true=Geometry.b5894 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5894

theorem bound5820 : BoxMajorant Geometry.b5820 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5820.Widths)
  · have he : Geometry.b5820.half 1 false=Geometry.b5853 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5853
  · have he : Geometry.b5820.half 1 true=Geometry.b5854 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5854

end N7.Kernel.Cover
