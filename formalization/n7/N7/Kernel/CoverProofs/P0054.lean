import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.PositiveGroups.G0041
import N7.Kernel.PositiveGroups.G0067
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2542 : BoxMajorant Geometry.b2542 := by
  exact PositiveLeaves.L2337.bound

theorem bound2541 : BoxMajorant Geometry.b2541 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2541 2 (by decide +kernel) x hx hd ho).elim

theorem bound2182 : BoxMajorant Geometry.b2182 := by
  exact PositiveLeaves.L2336.bound

theorem bound2181 : BoxMajorant Geometry.b2181 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2181.Widths)
  · have he : Geometry.b2181.half 1 false=Geometry.b2541 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2541
  · have he : Geometry.b2181.half 1 true=Geometry.b2542 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2542

theorem bound1560 : BoxMajorant Geometry.b1560 := by
  exact PositiveLeaves.L2334.bound

theorem bound1559 : BoxMajorant Geometry.b1559 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1559 2 (by decide +kernel) x hx hd ho).elim

theorem bound1558 : BoxMajorant Geometry.b1558 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1558.Widths)
  · have he : Geometry.b1558.half 0 false=Geometry.b2181 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2181
  · have he : Geometry.b1558.half 0 true=Geometry.b2182 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2182

theorem bound1557 : BoxMajorant Geometry.b1557 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1557 2 (by decide +kernel) x hx hd ho).elim

theorem bound1110 : BoxMajorant Geometry.b1110 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1110.Widths)
  · have he : Geometry.b1110.half 2 false=Geometry.b1559 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1559
  · have he : Geometry.b1110.half 2 true=Geometry.b1560 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1560

theorem bound1109 : BoxMajorant Geometry.b1109 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1109.Widths)
  · have he : Geometry.b1109.half 2 false=Geometry.b1557 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1557
  · have he : Geometry.b1109.half 2 true=Geometry.b1558 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1558

theorem bound806 : BoxMajorant Geometry.b806 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b806.Widths)
  · have he : Geometry.b806.half 1 false=Geometry.b1109 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1109
  · have he : Geometry.b806.half 1 true=Geometry.b1110 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1110

end N7.Kernel.Cover
