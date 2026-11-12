import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0427
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5426 : BoxMajorant Geometry.b5426 := by
  exact PositiveLeaves.L2847.bound

theorem bound5425 : BoxMajorant Geometry.b5425 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5425 2 (by decide +kernel) x hx hd ho).elim

theorem bound5424 : BoxMajorant Geometry.b5424 := by
  exact PositiveLeaves.L2849.bound

theorem bound5423 : BoxMajorant Geometry.b5423 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5423 2 (by decide +kernel) x hx hd ho).elim

theorem bound5422 : BoxMajorant Geometry.b5422 := by
  exact PositiveLeaves.L2851.bound

theorem bound5421 : BoxMajorant Geometry.b5421 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5421 2 (by decide +kernel) x hx hd ho).elim

theorem bound5298 : BoxMajorant Geometry.b5298 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5298.Widths)
  · have he : Geometry.b5298.half 2 false=Geometry.b5425 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5425
  · have he : Geometry.b5298.half 2 true=Geometry.b5426 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5426

theorem bound5297 : BoxMajorant Geometry.b5297 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5297.Widths)
  · have he : Geometry.b5297.half 2 false=Geometry.b5423 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5423
  · have he : Geometry.b5297.half 2 true=Geometry.b5424 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5424

theorem bound5296 : BoxMajorant Geometry.b5296 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5296.Widths)
  · have he : Geometry.b5296.half 2 false=Geometry.b5421 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5421
  · have he : Geometry.b5296.half 2 true=Geometry.b5422 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5422

theorem bound5295 : BoxMajorant Geometry.b5295 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5295 2 (by decide +kernel) x hx hd ho).elim

theorem bound5118 : BoxMajorant Geometry.b5118 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5118.Widths)
  · have he : Geometry.b5118.half 1 false=Geometry.b5297 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5297
  · have he : Geometry.b5118.half 1 true=Geometry.b5298 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5298

theorem bound5117 : BoxMajorant Geometry.b5117 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5117.Widths)
  · have he : Geometry.b5117.half 1 false=Geometry.b5295 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5295
  · have he : Geometry.b5117.half 1 true=Geometry.b5296 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5296

theorem bound4736 : BoxMajorant Geometry.b4736 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4736.Widths)
  · have he : Geometry.b4736.half 0 false=Geometry.b5117 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5117
  · have he : Geometry.b4736.half 0 true=Geometry.b5118 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5118

end N7.Kernel.Cover
