import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.PositiveGroups.G0000
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound580 : BoxMajorant Geometry.b580 := by
  exact PositiveLeaves.L1337.bound

theorem bound579 : BoxMajorant Geometry.b579 := by
  exact PositiveLeaves.L1338.bound

theorem bound372 : BoxMajorant Geometry.b372 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b372.Widths)
  · have he : Geometry.b372.half 2 false=Geometry.b579 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound579
  · have he : Geometry.b372.half 2 true=Geometry.b580 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound580

theorem bound371 : BoxMajorant Geometry.b371 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b371 0 (by decide +kernel) x hx hd ho).elim

theorem bound370 : BoxMajorant Geometry.b370 := by
  exact PositiveLeaves.L1341.bound

theorem bound369 : BoxMajorant Geometry.b369 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b369 0 (by decide +kernel) x hx hd ho).elim

theorem bound236 : BoxMajorant Geometry.b236 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b236 0 (by decide +kernel) x hx hd ho).elim

theorem bound235 : BoxMajorant Geometry.b235 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b235.Widths)
  · have he : Geometry.b235.half 1 false=Geometry.b371 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound371
  · have he : Geometry.b235.half 1 true=Geometry.b372 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound372

theorem bound234 : BoxMajorant Geometry.b234 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b234 0 (by decide +kernel) x hx hd ho).elim

theorem bound233 : BoxMajorant Geometry.b233 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b233.Widths)
  · have he : Geometry.b233.half 1 false=Geometry.b369 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound369
  · have he : Geometry.b233.half 1 true=Geometry.b370 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound370

theorem bound138 : BoxMajorant Geometry.b138 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b138.Widths)
  · have he : Geometry.b138.half 0 false=Geometry.b235 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound235
  · have he : Geometry.b138.half 0 true=Geometry.b236 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound236

theorem bound137 : BoxMajorant Geometry.b137 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b137.Widths)
  · have he : Geometry.b137.half 0 false=Geometry.b233 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound233
  · have he : Geometry.b137.half 0 true=Geometry.b234 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound234

theorem bound78 : BoxMajorant Geometry.b78 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b78.Widths)
  · have he : Geometry.b78.half 2 false=Geometry.b137 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound137
  · have he : Geometry.b78.half 2 true=Geometry.b138 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound138

theorem bound77 : BoxMajorant Geometry.b77 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b77 0 (by decide +kernel) x hx hd ho).elim

theorem bound41 : BoxMajorant Geometry.b41 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b41.Widths)
  · have he : Geometry.b41.half 1 false=Geometry.b77 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound77
  · have he : Geometry.b41.half 1 true=Geometry.b78 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound78

end N7.Kernel.Cover
