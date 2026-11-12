import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.PositiveGroups.G0047
import N7.Kernel.PositiveGroups.G0074
import N7.Kernel.PositiveGroups.G0075
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2530 : BoxMajorant Geometry.b2530 := by
  exact PositiveLeaves.L2388.bound

theorem bound2529 : BoxMajorant Geometry.b2529 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2529 2 (by decide +kernel) x hx hd ho).elim

theorem bound2172 : BoxMajorant Geometry.b2172 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2172.Widths)
  · have he : Geometry.b2172.half 1 false=Geometry.b2529 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2529
  · have he : Geometry.b2172.half 1 true=Geometry.b2530 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2530

theorem bound2171 : BoxMajorant Geometry.b2171 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2171 2 (by decide +kernel) x hx hd ho).elim

theorem bound1546 : BoxMajorant Geometry.b1546 := by
  exact PositiveLeaves.L2387.bound

theorem bound1545 : BoxMajorant Geometry.b1545 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1545.Widths)
  · have he : Geometry.b1545.half 0 false=Geometry.b2171 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2171
  · have he : Geometry.b1545.half 0 true=Geometry.b2172 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2172

theorem bound1100 : BoxMajorant Geometry.b1100 := by
  exact PositiveLeaves.L2386.bound

theorem bound1099 : BoxMajorant Geometry.b1099 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1099.Widths)
  · have he : Geometry.b1099.half 2 false=Geometry.b1545 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1545
  · have he : Geometry.b1099.half 2 true=Geometry.b1546 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1546

theorem bound798 : BoxMajorant Geometry.b798 := by
  exact PositiveLeaves.L2385.bound

theorem bound797 : BoxMajorant Geometry.b797 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b797.Widths)
  · have he : Geometry.b797.half 1 false=Geometry.b1099 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1099
  · have he : Geometry.b797.half 1 true=Geometry.b1100 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1100

theorem bound515 : BoxMajorant Geometry.b515 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b515.Widths)
  · have he : Geometry.b515.half 0 false=Geometry.b797 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound797
  · have he : Geometry.b515.half 0 true=Geometry.b798 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound798

end N7.Kernel.Cover
