import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverGeometry.G0092
import N7.Kernel.PositiveGroups.G0498
import N7.Kernel.PositiveGroups.G0499
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5900 : BoxMajorant Geometry.b5900 := by
  exact PositiveLeaves.L389.bound

theorem bound5899 : BoxMajorant Geometry.b5899 := by
  exact PositiveLeaves.L390.bound

theorem bound5898 : BoxMajorant Geometry.b5898 := by
  exact PositiveLeaves.L391.bound

theorem bound5897 : BoxMajorant Geometry.b5897 := by
  exact PositiveLeaves.L392.bound

theorem bound5856 : BoxMajorant Geometry.b5856 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5856.Widths)
  · have he : Geometry.b5856.half 2 false=Geometry.b5899 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5899
  · have he : Geometry.b5856.half 2 true=Geometry.b5900 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5900

theorem bound5855 : BoxMajorant Geometry.b5855 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5855.Widths)
  · have he : Geometry.b5855.half 2 false=Geometry.b5897 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5897
  · have he : Geometry.b5855.half 2 true=Geometry.b5898 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5898

theorem bound5822 : BoxMajorant Geometry.b5822 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5822.Widths)
  · have he : Geometry.b5822.half 1 false=Geometry.b5855 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5855
  · have he : Geometry.b5822.half 1 true=Geometry.b5856 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5856

end N7.Kernel.Cover
