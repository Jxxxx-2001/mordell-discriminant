import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0455
import N7.Kernel.PositiveGroups.G0456
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5440 : BoxMajorant Geometry.b5440 := by
  exact PositiveLeaves.L2823.bound

theorem bound5439 : BoxMajorant Geometry.b5439 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5439 2 (by decide +kernel) x hx hd ho).elim

theorem bound5438 : BoxMajorant Geometry.b5438 := by
  exact PositiveLeaves.L2825.bound

theorem bound5437 : BoxMajorant Geometry.b5437 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5437 2 (by decide +kernel) x hx hd ho).elim

theorem bound5310 : BoxMajorant Geometry.b5310 := by
  exact PositiveLeaves.L2822.bound

theorem bound5309 : BoxMajorant Geometry.b5309 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5309.Widths)
  · have he : Geometry.b5309.half 2 false=Geometry.b5439 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5439
  · have he : Geometry.b5309.half 2 true=Geometry.b5440 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5440

theorem bound5308 : BoxMajorant Geometry.b5308 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5308.Widths)
  · have he : Geometry.b5308.half 2 false=Geometry.b5437 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5437
  · have he : Geometry.b5308.half 2 true=Geometry.b5438 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5438

theorem bound5307 : BoxMajorant Geometry.b5307 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5307 2 (by decide +kernel) x hx hd ho).elim

theorem bound5126 : BoxMajorant Geometry.b5126 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5126.Widths)
  · have he : Geometry.b5126.half 1 false=Geometry.b5309 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5309
  · have he : Geometry.b5126.half 1 true=Geometry.b5310 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5310

theorem bound5125 : BoxMajorant Geometry.b5125 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5125.Widths)
  · have he : Geometry.b5125.half 1 false=Geometry.b5307 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5307
  · have he : Geometry.b5125.half 1 true=Geometry.b5308 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5308

theorem bound4743 : BoxMajorant Geometry.b4743 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4743.Widths)
  · have he : Geometry.b4743.half 0 false=Geometry.b5125 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5125
  · have he : Geometry.b4743.half 0 true=Geometry.b5126 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5126

end N7.Kernel.Cover
