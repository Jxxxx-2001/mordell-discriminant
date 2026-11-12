import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.PositiveGroups.G0069
import N7.Kernel.PositiveGroups.G0070
import N7.Kernel.PositiveGroups.G0105
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2912 : BoxMajorant Geometry.b2912 := by
  exact PositiveLeaves.L2234.bound

theorem bound2911 : BoxMajorant Geometry.b2911 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2911 2 (by decide +kernel) x hx hd ho).elim

theorem bound2566 : BoxMajorant Geometry.b2566 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2566.Widths)
  · have he : Geometry.b2566.half 2 false=Geometry.b2911 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2911
  · have he : Geometry.b2566.half 2 true=Geometry.b2912 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2912

theorem bound2565 : BoxMajorant Geometry.b2565 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2565 2 (by decide +kernel) x hx hd ho).elim

theorem bound2204 : BoxMajorant Geometry.b2204 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2204.Widths)
  · have he : Geometry.b2204.half 1 false=Geometry.b2565 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2565
  · have he : Geometry.b2204.half 1 true=Geometry.b2566 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2566

theorem bound2203 : BoxMajorant Geometry.b2203 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2203 2 (by decide +kernel) x hx hd ho).elim

theorem bound1600 : BoxMajorant Geometry.b1600 := by
  exact PositiveLeaves.L2230.bound

theorem bound1599 : BoxMajorant Geometry.b1599 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1599 2 (by decide +kernel) x hx hd ho).elim

theorem bound1598 : BoxMajorant Geometry.b1598 := by
  exact PositiveLeaves.L2232.bound

theorem bound1597 : BoxMajorant Geometry.b1597 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1597 2 (by decide +kernel) x hx hd ho).elim

theorem bound1596 : BoxMajorant Geometry.b1596 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1596.Widths)
  · have he : Geometry.b1596.half 0 false=Geometry.b2203 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2203
  · have he : Geometry.b1596.half 0 true=Geometry.b2204 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2204

theorem bound1595 : BoxMajorant Geometry.b1595 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1595 2 (by decide +kernel) x hx hd ho).elim

theorem bound1136 : BoxMajorant Geometry.b1136 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1136.Widths)
  · have he : Geometry.b1136.half 2 false=Geometry.b1599 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1599
  · have he : Geometry.b1136.half 2 true=Geometry.b1600 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1600

theorem bound1135 : BoxMajorant Geometry.b1135 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1135.Widths)
  · have he : Geometry.b1135.half 2 false=Geometry.b1597 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1597
  · have he : Geometry.b1135.half 2 true=Geometry.b1598 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1598

theorem bound1134 : BoxMajorant Geometry.b1134 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1134.Widths)
  · have he : Geometry.b1134.half 2 false=Geometry.b1595 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1595
  · have he : Geometry.b1134.half 2 true=Geometry.b1596 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1596

theorem bound1133 : BoxMajorant Geometry.b1133 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1133 2 (by decide +kernel) x hx hd ho).elim

theorem bound824 : BoxMajorant Geometry.b824 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b824.Widths)
  · have he : Geometry.b824.half 1 false=Geometry.b1135 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1135
  · have he : Geometry.b824.half 1 true=Geometry.b1136 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1136

theorem bound823 : BoxMajorant Geometry.b823 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b823.Widths)
  · have he : Geometry.b823.half 1 false=Geometry.b1133 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1133
  · have he : Geometry.b823.half 1 true=Geometry.b1134 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1134

theorem bound543 : BoxMajorant Geometry.b543 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b543.Widths)
  · have he : Geometry.b543.half 0 false=Geometry.b823 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound823
  · have he : Geometry.b543.half 0 true=Geometry.b824 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound824

end N7.Kernel.Cover
