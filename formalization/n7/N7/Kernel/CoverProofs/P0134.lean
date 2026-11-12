import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0029
import N7.Kernel.PositiveGroups.G0082
import N7.Kernel.PositiveGroups.G0158
import N7.Kernel.PositiveGroups.G0208
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1872 : BoxMajorant Geometry.b1872 := by
  exact PositiveLeaves.L772.bound

theorem bound1871 : BoxMajorant Geometry.b1871 := by
  exact PositiveLeaves.L773.bound

theorem bound1300 : BoxMajorant Geometry.b1300 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1300.Widths)
  · have he : Geometry.b1300.half 2 false=Geometry.b1871 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1871
  · have he : Geometry.b1300.half 2 true=Geometry.b1872 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1872

theorem bound1299 : BoxMajorant Geometry.b1299 := by
  exact PositiveLeaves.L774.bound

theorem bound938 : BoxMajorant Geometry.b938 := by
  exact PositiveLeaves.L771.bound

theorem bound937 : BoxMajorant Geometry.b937 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b937.Widths)
  · have he : Geometry.b937.half 1 false=Geometry.b1299 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1299
  · have he : Geometry.b937.half 1 true=Geometry.b1300 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1300

theorem bound647 : BoxMajorant Geometry.b647 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b647.Widths)
  · have he : Geometry.b647.half 0 false=Geometry.b937 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound937
  · have he : Geometry.b647.half 0 true=Geometry.b938 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound938

end N7.Kernel.Cover
