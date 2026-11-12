import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0439
import N7.Kernel.PositiveGroups.G0440
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5450 : BoxMajorant Geometry.b5450 := by
  exact PositiveLeaves.L2804.bound

theorem bound5449 : BoxMajorant Geometry.b5449 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5449 2 (by decide +kernel) x hx hd ho).elim

theorem bound5448 : BoxMajorant Geometry.b5448 := by
  exact PositiveLeaves.L2806.bound

theorem bound5447 : BoxMajorant Geometry.b5447 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5447 2 (by decide +kernel) x hx hd ho).elim

theorem bound5446 : BoxMajorant Geometry.b5446 := by
  exact PositiveLeaves.L2808.bound

theorem bound5445 : BoxMajorant Geometry.b5445 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5445 2 (by decide +kernel) x hx hd ho).elim

theorem bound5318 : BoxMajorant Geometry.b5318 := by
  exact PositiveLeaves.L2803.bound

theorem bound5317 : BoxMajorant Geometry.b5317 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5317.Widths)
  · have he : Geometry.b5317.half 2 false=Geometry.b5449 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5449
  · have he : Geometry.b5317.half 2 true=Geometry.b5450 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5450

theorem bound5316 : BoxMajorant Geometry.b5316 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5316.Widths)
  · have he : Geometry.b5316.half 2 false=Geometry.b5447 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5447
  · have he : Geometry.b5316.half 2 true=Geometry.b5448 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5448

theorem bound5315 : BoxMajorant Geometry.b5315 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5315.Widths)
  · have he : Geometry.b5315.half 2 false=Geometry.b5445 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5445
  · have he : Geometry.b5315.half 2 true=Geometry.b5446 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5446

theorem bound5130 : BoxMajorant Geometry.b5130 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5130.Widths)
  · have he : Geometry.b5130.half 1 false=Geometry.b5317 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5317
  · have he : Geometry.b5130.half 1 true=Geometry.b5318 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5318

theorem bound5129 : BoxMajorant Geometry.b5129 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5129.Widths)
  · have he : Geometry.b5129.half 1 false=Geometry.b5315 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5315
  · have he : Geometry.b5129.half 1 true=Geometry.b5316 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5316

theorem bound4748 : BoxMajorant Geometry.b4748 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4748.Widths)
  · have he : Geometry.b4748.half 0 false=Geometry.b5129 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5129
  · have he : Geometry.b4748.half 0 true=Geometry.b5130 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5130

end N7.Kernel.Cover
