import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0452
import N7.Kernel.PositiveGroups.G0453
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5466 : BoxMajorant Geometry.b5466 := by
  exact PositiveLeaves.L2610.bound

theorem bound5465 : BoxMajorant Geometry.b5465 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5465 2 (by decide +kernel) x hx hd ho).elim

theorem bound5464 : BoxMajorant Geometry.b5464 := by
  exact PositiveLeaves.L2612.bound

theorem bound5463 : BoxMajorant Geometry.b5463 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5463 2 (by decide +kernel) x hx hd ho).elim

theorem bound5336 : BoxMajorant Geometry.b5336 := by
  exact PositiveLeaves.L2609.bound

theorem bound5335 : BoxMajorant Geometry.b5335 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5335.Widths)
  · have he : Geometry.b5335.half 2 false=Geometry.b5465 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5465
  · have he : Geometry.b5335.half 2 true=Geometry.b5466 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5466

theorem bound5334 : BoxMajorant Geometry.b5334 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5334.Widths)
  · have he : Geometry.b5334.half 2 false=Geometry.b5463 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5463
  · have he : Geometry.b5334.half 2 true=Geometry.b5464 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5464

theorem bound5333 : BoxMajorant Geometry.b5333 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5333 2 (by decide +kernel) x hx hd ho).elim

theorem bound5152 : BoxMajorant Geometry.b5152 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5152.Widths)
  · have he : Geometry.b5152.half 1 false=Geometry.b5335 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5335
  · have he : Geometry.b5152.half 1 true=Geometry.b5336 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5336

theorem bound5151 : BoxMajorant Geometry.b5151 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5151.Widths)
  · have he : Geometry.b5151.half 1 false=Geometry.b5333 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5333
  · have he : Geometry.b5151.half 1 true=Geometry.b5334 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5334

theorem bound4793 : BoxMajorant Geometry.b4793 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4793.Widths)
  · have he : Geometry.b4793.half 0 false=Geometry.b5151 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5151
  · have he : Geometry.b4793.half 0 true=Geometry.b5152 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5152

end N7.Kernel.Cover
