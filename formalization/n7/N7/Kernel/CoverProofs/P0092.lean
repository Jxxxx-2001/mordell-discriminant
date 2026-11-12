import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.PositiveGroups.G0093
import N7.Kernel.PositiveGroups.G0094
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1682 : BoxMajorant Geometry.b1682 := by
  exact PositiveLeaves.L1173.bound

theorem bound1681 : BoxMajorant Geometry.b1681 := by
  exact PositiveLeaves.L1174.bound

theorem bound1188 : BoxMajorant Geometry.b1188 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1188.Widths)
  · have he : Geometry.b1188.half 2 false=Geometry.b1681 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1681
  · have he : Geometry.b1188.half 2 true=Geometry.b1682 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1682

theorem bound1187 : BoxMajorant Geometry.b1187 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1187 0 (by decide +kernel) x hx hd ho).elim

theorem bound865 : BoxMajorant Geometry.b865 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b865.Widths)
  · have he : Geometry.b865.half 1 false=Geometry.b1187 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1187
  · have he : Geometry.b865.half 1 true=Geometry.b1188 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1188

end N7.Kernel.Cover
