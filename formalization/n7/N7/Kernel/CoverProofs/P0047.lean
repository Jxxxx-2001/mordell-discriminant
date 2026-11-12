import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.PositiveGroups.G0047
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1544 : BoxMajorant Geometry.b1544 := by
  exact PositiveLeaves.L2393.bound

theorem bound1543 : BoxMajorant Geometry.b1543 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1543 2 (by decide +kernel) x hx hd ho).elim

theorem bound1098 : BoxMajorant Geometry.b1098 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1098.Widths)
  · have he : Geometry.b1098.half 2 false=Geometry.b1543 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1543
  · have he : Geometry.b1098.half 2 true=Geometry.b1544 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1544

theorem bound1097 : BoxMajorant Geometry.b1097 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1097 0 (by decide +kernel) x hx hd ho).elim

theorem bound796 : BoxMajorant Geometry.b796 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b796 0 (by decide +kernel) x hx hd ho).elim

theorem bound795 : BoxMajorant Geometry.b795 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b795.Widths)
  · have he : Geometry.b795.half 1 false=Geometry.b1097 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1097
  · have he : Geometry.b795.half 1 true=Geometry.b1098 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1098

theorem bound513 : BoxMajorant Geometry.b513 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b513.Widths)
  · have he : Geometry.b513.half 0 false=Geometry.b795 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound795
  · have he : Geometry.b513.half 0 true=Geometry.b796 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound796

end N7.Kernel.Cover
