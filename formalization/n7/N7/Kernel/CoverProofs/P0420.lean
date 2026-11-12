import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverGeometry.G0092
import N7.Kernel.PositiveGroups.G0503
import N7.Kernel.PositiveGroups.G0504
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5892 : BoxMajorant Geometry.b5892 := by
  exact PositiveLeaves.L400.bound

theorem bound5891 : BoxMajorant Geometry.b5891 := by
  exact PositiveLeaves.L401.bound

theorem bound5890 : BoxMajorant Geometry.b5890 := by
  exact PositiveLeaves.L402.bound

theorem bound5889 : BoxMajorant Geometry.b5889 := by
  exact PositiveLeaves.L403.bound

theorem bound5852 : BoxMajorant Geometry.b5852 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5852.Widths)
  · have he : Geometry.b5852.half 2 false=Geometry.b5891 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5891
  · have he : Geometry.b5852.half 2 true=Geometry.b5892 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5892

theorem bound5851 : BoxMajorant Geometry.b5851 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5851.Widths)
  · have he : Geometry.b5851.half 2 false=Geometry.b5889 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5889
  · have he : Geometry.b5851.half 2 true=Geometry.b5890 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5890

theorem bound5819 : BoxMajorant Geometry.b5819 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5819.Widths)
  · have he : Geometry.b5819.half 1 false=Geometry.b5851 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5851
  · have he : Geometry.b5819.half 1 true=Geometry.b5852 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5852

end N7.Kernel.Cover
