import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.PositiveGroups.G0128
import N7.Kernel.PositiveGroups.G0168
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2312 : BoxMajorant Geometry.b2312 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2312 0 (by decide +kernel) x hx hd ho).elim

theorem bound2311 : BoxMajorant Geometry.b2311 := by
  exact PositiveLeaves.L1050.bound

theorem bound1764 : BoxMajorant Geometry.b1764 := by
  exact PositiveLeaves.L1048.bound

theorem bound1763 : BoxMajorant Geometry.b1763 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1763.Widths)
  · have he : Geometry.b1763.half 0 false=Geometry.b2311 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2311
  · have he : Geometry.b1763.half 0 true=Geometry.b2312 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2312

theorem bound1236 : BoxMajorant Geometry.b1236 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1236.Widths)
  · have he : Geometry.b1236.half 2 false=Geometry.b1763 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1763
  · have he : Geometry.b1236.half 2 true=Geometry.b1764 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1764

theorem bound1235 : BoxMajorant Geometry.b1235 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1235 0 (by decide +kernel) x hx hd ho).elim

theorem bound898 : BoxMajorant Geometry.b898 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b898 0 (by decide +kernel) x hx hd ho).elim

theorem bound897 : BoxMajorant Geometry.b897 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b897.Widths)
  · have he : Geometry.b897.half 1 false=Geometry.b1235 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1235
  · have he : Geometry.b897.half 1 true=Geometry.b1236 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1236

theorem bound615 : BoxMajorant Geometry.b615 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b615.Widths)
  · have he : Geometry.b615.half 0 false=Geometry.b897 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound897
  · have he : Geometry.b615.half 0 true=Geometry.b898 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound898

end N7.Kernel.Cover
