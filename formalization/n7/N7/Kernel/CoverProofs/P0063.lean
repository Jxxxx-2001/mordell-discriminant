import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.PositiveGroups.G0044
import N7.Kernel.PositiveGroups.G0069
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1586 : BoxMajorant Geometry.b1586 := by
  exact PositiveLeaves.L2253.bound

theorem bound1585 : BoxMajorant Geometry.b1585 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1585 2 (by decide +kernel) x hx hd ho).elim

theorem bound1128 : BoxMajorant Geometry.b1128 := by
  exact PositiveLeaves.L2252.bound

theorem bound1127 : BoxMajorant Geometry.b1127 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1127.Widths)
  · have he : Geometry.b1127.half 2 false=Geometry.b1585 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1585
  · have he : Geometry.b1127.half 2 true=Geometry.b1586 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1586

theorem bound818 : BoxMajorant Geometry.b818 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b818.Widths)
  · have he : Geometry.b818.half 1 false=Geometry.b1127 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1127
  · have he : Geometry.b818.half 1 true=Geometry.b1128 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1128

theorem bound817 : BoxMajorant Geometry.b817 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b817 2 (by decide +kernel) x hx hd ho).elim

theorem bound538 : BoxMajorant Geometry.b538 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b538.Widths)
  · have he : Geometry.b538.half 0 false=Geometry.b817 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound817
  · have he : Geometry.b538.half 0 true=Geometry.b818 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound818

end N7.Kernel.Cover
