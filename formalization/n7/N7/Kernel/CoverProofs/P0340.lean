import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0453
import N7.Kernel.PositiveGroups.G0454
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5432 : BoxMajorant Geometry.b5432 := by
  exact PositiveLeaves.L2839.bound

theorem bound5431 : BoxMajorant Geometry.b5431 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5431 2 (by decide +kernel) x hx hd ho).elim

theorem bound5430 : BoxMajorant Geometry.b5430 := by
  exact PositiveLeaves.L2841.bound

theorem bound5429 : BoxMajorant Geometry.b5429 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5429 2 (by decide +kernel) x hx hd ho).elim

theorem bound5428 : BoxMajorant Geometry.b5428 := by
  exact PositiveLeaves.L2843.bound

theorem bound5427 : BoxMajorant Geometry.b5427 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5427 2 (by decide +kernel) x hx hd ho).elim

theorem bound5302 : BoxMajorant Geometry.b5302 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5302.Widths)
  · have he : Geometry.b5302.half 2 false=Geometry.b5431 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5431
  · have he : Geometry.b5302.half 2 true=Geometry.b5432 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5432

theorem bound5301 : BoxMajorant Geometry.b5301 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5301.Widths)
  · have he : Geometry.b5301.half 2 false=Geometry.b5429 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5429
  · have he : Geometry.b5301.half 2 true=Geometry.b5430 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5430

theorem bound5300 : BoxMajorant Geometry.b5300 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5300.Widths)
  · have he : Geometry.b5300.half 2 false=Geometry.b5427 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5427
  · have he : Geometry.b5300.half 2 true=Geometry.b5428 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5428

theorem bound5299 : BoxMajorant Geometry.b5299 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5299 2 (by decide +kernel) x hx hd ho).elim

theorem bound5120 : BoxMajorant Geometry.b5120 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5120.Widths)
  · have he : Geometry.b5120.half 1 false=Geometry.b5301 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5301
  · have he : Geometry.b5120.half 1 true=Geometry.b5302 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5302

theorem bound5119 : BoxMajorant Geometry.b5119 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5119.Widths)
  · have he : Geometry.b5119.half 1 false=Geometry.b5299 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5299
  · have he : Geometry.b5119.half 1 true=Geometry.b5300 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5300

theorem bound4738 : BoxMajorant Geometry.b4738 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4738.Widths)
  · have he : Geometry.b4738.half 0 false=Geometry.b5119 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5119
  · have he : Geometry.b4738.half 0 true=Geometry.b5120 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5120

end N7.Kernel.Cover
