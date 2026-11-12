import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0442
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5412 : BoxMajorant Geometry.b5412 := by
  exact PositiveLeaves.L2870.bound

theorem bound5411 : BoxMajorant Geometry.b5411 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5411 2 (by decide +kernel) x hx hd ho).elim

theorem bound5288 : BoxMajorant Geometry.b5288 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5288.Widths)
  · have he : Geometry.b5288.half 2 false=Geometry.b5411 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5411
  · have he : Geometry.b5288.half 2 true=Geometry.b5412 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5412

theorem bound5287 : BoxMajorant Geometry.b5287 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5287 2 (by decide +kernel) x hx hd ho).elim

theorem bound5112 : BoxMajorant Geometry.b5112 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5112.Widths)
  · have he : Geometry.b5112.half 1 false=Geometry.b5287 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5287
  · have he : Geometry.b5112.half 1 true=Geometry.b5288 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5288

theorem bound5111 : BoxMajorant Geometry.b5111 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5111 2 (by decide +kernel) x hx hd ho).elim

theorem bound4730 : BoxMajorant Geometry.b4730 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4730.Widths)
  · have he : Geometry.b4730.half 0 false=Geometry.b5111 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5111
  · have he : Geometry.b4730.half 0 true=Geometry.b5112 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5112

end N7.Kernel.Cover
