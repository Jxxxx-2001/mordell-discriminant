import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.PositiveGroups.G0025
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2532 : BoxMajorant Geometry.b2532 := by
  exact PositiveLeaves.L2363.bound

theorem bound2531 : BoxMajorant Geometry.b2531 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2531 2 (by decide +kernel) x hx hd ho).elim

theorem bound2174 : BoxMajorant Geometry.b2174 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2174.Widths)
  · have he : Geometry.b2174.half 1 false=Geometry.b2531 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2531
  · have he : Geometry.b2174.half 1 true=Geometry.b2532 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2532

theorem bound2173 : BoxMajorant Geometry.b2173 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2173 2 (by decide +kernel) x hx hd ho).elim

theorem bound1550 : BoxMajorant Geometry.b1550 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1550.Widths)
  · have he : Geometry.b1550.half 0 false=Geometry.b2173 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2173
  · have he : Geometry.b1550.half 0 true=Geometry.b2174 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2174

theorem bound1549 : BoxMajorant Geometry.b1549 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1549 2 (by decide +kernel) x hx hd ho).elim

theorem bound1104 : BoxMajorant Geometry.b1104 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1104.Widths)
  · have he : Geometry.b1104.half 2 false=Geometry.b1549 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1549
  · have he : Geometry.b1104.half 2 true=Geometry.b1550 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1550

theorem bound1103 : BoxMajorant Geometry.b1103 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1103 2 (by decide +kernel) x hx hd ho).elim

theorem bound802 : BoxMajorant Geometry.b802 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b802.Widths)
  · have he : Geometry.b802.half 1 false=Geometry.b1103 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1103
  · have he : Geometry.b802.half 1 true=Geometry.b1104 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1104

theorem bound801 : BoxMajorant Geometry.b801 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b801 2 (by decide +kernel) x hx hd ho).elim

theorem bound524 : BoxMajorant Geometry.b524 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b524.Widths)
  · have he : Geometry.b524.half 0 false=Geometry.b801 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound801
  · have he : Geometry.b524.half 0 true=Geometry.b802 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound802

theorem bound523 : BoxMajorant Geometry.b523 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b523 2 (by decide +kernel) x hx hd ho).elim

theorem bound334 : BoxMajorant Geometry.b334 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b334.Widths)
  · have he : Geometry.b334.half 2 false=Geometry.b523 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound523
  · have he : Geometry.b334.half 2 true=Geometry.b524 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound524

theorem bound333 : BoxMajorant Geometry.b333 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b333 2 (by decide +kernel) x hx hd ho).elim

theorem bound210 : BoxMajorant Geometry.b210 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b210.Widths)
  · have he : Geometry.b210.half 1 false=Geometry.b333 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound333
  · have he : Geometry.b210.half 1 true=Geometry.b334 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound334

theorem bound209 : BoxMajorant Geometry.b209 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b209 2 (by decide +kernel) x hx hd ho).elim

theorem bound122 : BoxMajorant Geometry.b122 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b122.Widths)
  · have he : Geometry.b122.half 0 false=Geometry.b209 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound209
  · have he : Geometry.b122.half 0 true=Geometry.b210 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound210

theorem bound121 : BoxMajorant Geometry.b121 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b121 2 (by decide +kernel) x hx hd ho).elim

theorem bound68 : BoxMajorant Geometry.b68 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b68.Widths)
  · have he : Geometry.b68.half 2 false=Geometry.b121 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound121
  · have he : Geometry.b68.half 2 true=Geometry.b122 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound122

theorem bound67 : BoxMajorant Geometry.b67 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b67 2 (by decide +kernel) x hx hd ho).elim

theorem bound35 : BoxMajorant Geometry.b35 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b35.Widths)
  · have he : Geometry.b35.half 1 false=Geometry.b67 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound67
  · have he : Geometry.b35.half 1 true=Geometry.b68 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound68

end N7.Kernel.Cover
