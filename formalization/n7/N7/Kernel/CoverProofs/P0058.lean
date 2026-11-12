import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.PositiveGroups.G0020
import N7.Kernel.PositiveGroups.G0040
import N7.Kernel.PositiveGroups.G0066
import N7.Kernel.PositiveGroups.G0101
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2900 : BoxMajorant Geometry.b2900 := by
  exact PositiveLeaves.L2295.bound

theorem bound2899 : BoxMajorant Geometry.b2899 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2899 2 (by decide +kernel) x hx hd ho).elim

theorem bound2898 : BoxMajorant Geometry.b2898 := by
  exact PositiveLeaves.L2299.bound

theorem bound2897 : BoxMajorant Geometry.b2897 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2897 2 (by decide +kernel) x hx hd ho).elim

theorem bound2896 : BoxMajorant Geometry.b2896 := by
  exact PositiveLeaves.L2301.bound

theorem bound2895 : BoxMajorant Geometry.b2895 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2895 2 (by decide +kernel) x hx hd ho).elim

theorem bound2554 : BoxMajorant Geometry.b2554 := by
  exact PositiveLeaves.L2294.bound

theorem bound2553 : BoxMajorant Geometry.b2553 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2553.Widths)
  · have he : Geometry.b2553.half 2 false=Geometry.b2899 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2899
  · have he : Geometry.b2553.half 2 true=Geometry.b2900 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2900

theorem bound2552 : BoxMajorant Geometry.b2552 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2552.Widths)
  · have he : Geometry.b2552.half 2 false=Geometry.b2897 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2897
  · have he : Geometry.b2552.half 2 true=Geometry.b2898 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2898

theorem bound2551 : BoxMajorant Geometry.b2551 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2551.Widths)
  · have he : Geometry.b2551.half 2 false=Geometry.b2895 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2895
  · have he : Geometry.b2551.half 2 true=Geometry.b2896 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2896

theorem bound2194 : BoxMajorant Geometry.b2194 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2194.Widths)
  · have he : Geometry.b2194.half 1 false=Geometry.b2553 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2553
  · have he : Geometry.b2194.half 1 true=Geometry.b2554 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2554

theorem bound2193 : BoxMajorant Geometry.b2193 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2193 2 (by decide +kernel) x hx hd ho).elim

theorem bound2192 : BoxMajorant Geometry.b2192 := by
  exact PositiveLeaves.L2298.bound

theorem bound2191 : BoxMajorant Geometry.b2191 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2191.Widths)
  · have he : Geometry.b2191.half 1 false=Geometry.b2551 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2551
  · have he : Geometry.b2191.half 1 true=Geometry.b2552 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2552

theorem bound1574 : BoxMajorant Geometry.b1574 := by
  exact PositiveLeaves.L2293.bound

theorem bound1573 : BoxMajorant Geometry.b1573 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1573.Widths)
  · have he : Geometry.b1573.half 0 false=Geometry.b2193 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2193
  · have he : Geometry.b1573.half 0 true=Geometry.b2194 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2194

theorem bound1572 : BoxMajorant Geometry.b1572 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1572.Widths)
  · have he : Geometry.b1572.half 0 false=Geometry.b2191 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2191
  · have he : Geometry.b1572.half 0 true=Geometry.b2192 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2192

theorem bound1571 : BoxMajorant Geometry.b1571 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1571 2 (by decide +kernel) x hx hd ho).elim

theorem bound1118 : BoxMajorant Geometry.b1118 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1118.Widths)
  · have he : Geometry.b1118.half 2 false=Geometry.b1573 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1573
  · have he : Geometry.b1118.half 2 true=Geometry.b1574 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1574

theorem bound1117 : BoxMajorant Geometry.b1117 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1117.Widths)
  · have he : Geometry.b1117.half 2 false=Geometry.b1571 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1571
  · have he : Geometry.b1117.half 2 true=Geometry.b1572 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1572

theorem bound810 : BoxMajorant Geometry.b810 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b810.Widths)
  · have he : Geometry.b810.half 1 false=Geometry.b1117 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1117
  · have he : Geometry.b810.half 1 true=Geometry.b1118 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1118

end N7.Kernel.Cover
