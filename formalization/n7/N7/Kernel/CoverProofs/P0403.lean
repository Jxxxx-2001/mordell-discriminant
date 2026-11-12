import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.PositiveGroups.G0459
import N7.Kernel.PositiveGroups.G0464
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5552 : BoxMajorant Geometry.b5552 := by
  exact PositiveLeaves.L193.bound

theorem bound5551 : BoxMajorant Geometry.b5551 := by
  exact PositiveLeaves.L194.bound

theorem bound5400 : BoxMajorant Geometry.b5400 := by
  exact PositiveLeaves.L192.bound

theorem bound5399 : BoxMajorant Geometry.b5399 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5399.Widths)
  · have he : Geometry.b5399.half 2 false=Geometry.b5551 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5551
  · have he : Geometry.b5399.half 2 true=Geometry.b5552 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5552

theorem bound5278 : BoxMajorant Geometry.b5278 := by
  exact PositiveLeaves.L191.bound

theorem bound5277 : BoxMajorant Geometry.b5277 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5277.Widths)
  · have he : Geometry.b5277.half 1 false=Geometry.b5399 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5399
  · have he : Geometry.b5277.half 1 true=Geometry.b5400 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5400

theorem bound5100 : BoxMajorant Geometry.b5100 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5100.Widths)
  · have he : Geometry.b5100.half 0 false=Geometry.b5277 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5277
  · have he : Geometry.b5100.half 0 true=Geometry.b5278 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5278

theorem bound5099 : BoxMajorant Geometry.b5099 := by
  exact PositiveLeaves.L195.bound

theorem bound4711 : BoxMajorant Geometry.b4711 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4711.Widths)
  · have he : Geometry.b4711.half 2 false=Geometry.b5099 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5099
  · have he : Geometry.b4711.half 2 true=Geometry.b5100 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5100

end N7.Kernel.Cover
