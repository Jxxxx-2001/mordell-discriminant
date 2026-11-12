import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0427
import N7.Kernel.PositiveGroups.G0428
import N7.Kernel.PositiveGroups.G0442
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5418 : BoxMajorant Geometry.b5418 := by
  exact PositiveLeaves.L2862.bound

theorem bound5417 : BoxMajorant Geometry.b5417 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5417 2 (by decide +kernel) x hx hd ho).elim

theorem bound5416 : BoxMajorant Geometry.b5416 := by
  exact PositiveLeaves.L2864.bound

theorem bound5415 : BoxMajorant Geometry.b5415 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5415 2 (by decide +kernel) x hx hd ho).elim

theorem bound5414 : BoxMajorant Geometry.b5414 := by
  exact PositiveLeaves.L2866.bound

theorem bound5413 : BoxMajorant Geometry.b5413 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5413 2 (by decide +kernel) x hx hd ho).elim

theorem bound5292 : BoxMajorant Geometry.b5292 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5292.Widths)
  · have he : Geometry.b5292.half 2 false=Geometry.b5417 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5417
  · have he : Geometry.b5292.half 2 true=Geometry.b5418 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5418

theorem bound5291 : BoxMajorant Geometry.b5291 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5291.Widths)
  · have he : Geometry.b5291.half 2 false=Geometry.b5415 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5415
  · have he : Geometry.b5291.half 2 true=Geometry.b5416 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5416

theorem bound5290 : BoxMajorant Geometry.b5290 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5290.Widths)
  · have he : Geometry.b5290.half 2 false=Geometry.b5413 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5413
  · have he : Geometry.b5290.half 2 true=Geometry.b5414 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5414

theorem bound5289 : BoxMajorant Geometry.b5289 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5289 2 (by decide +kernel) x hx hd ho).elim

theorem bound5114 : BoxMajorant Geometry.b5114 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5114.Widths)
  · have he : Geometry.b5114.half 1 false=Geometry.b5291 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5291
  · have he : Geometry.b5114.half 1 true=Geometry.b5292 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5292

theorem bound5113 : BoxMajorant Geometry.b5113 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5113.Widths)
  · have he : Geometry.b5113.half 1 false=Geometry.b5289 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5289
  · have he : Geometry.b5113.half 1 true=Geometry.b5290 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5290

theorem bound4732 : BoxMajorant Geometry.b4732 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4732.Widths)
  · have he : Geometry.b4732.half 0 false=Geometry.b5113 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5113
  · have he : Geometry.b4732.half 0 true=Geometry.b5114 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5114

end N7.Kernel.Cover
