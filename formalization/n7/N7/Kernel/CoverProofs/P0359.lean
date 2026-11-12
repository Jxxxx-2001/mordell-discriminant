import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0438
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5468 : BoxMajorant Geometry.b5468 := by
  exact PositiveLeaves.L2605.bound

theorem bound5467 : BoxMajorant Geometry.b5467 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5467 2 (by decide +kernel) x hx hd ho).elim

theorem bound5338 : BoxMajorant Geometry.b5338 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5338.Widths)
  · have he : Geometry.b5338.half 2 false=Geometry.b5467 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5467
  · have he : Geometry.b5338.half 2 true=Geometry.b5468 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5468

theorem bound5337 : BoxMajorant Geometry.b5337 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5337 0 (by decide +kernel) x hx hd ho).elim

theorem bound5154 : BoxMajorant Geometry.b5154 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5154 0 (by decide +kernel) x hx hd ho).elim

theorem bound5153 : BoxMajorant Geometry.b5153 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5153.Widths)
  · have he : Geometry.b5153.half 1 false=Geometry.b5337 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5337
  · have he : Geometry.b5153.half 1 true=Geometry.b5338 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5338

theorem bound4795 : BoxMajorant Geometry.b4795 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4795.Widths)
  · have he : Geometry.b4795.half 0 false=Geometry.b5153 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5153
  · have he : Geometry.b4795.half 0 true=Geometry.b5154 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5154

end N7.Kernel.Cover
