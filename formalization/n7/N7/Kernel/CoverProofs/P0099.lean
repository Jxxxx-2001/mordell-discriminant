import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.PositiveGroups.G0134
import N7.Kernel.PositiveGroups.G0170
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1708 : BoxMajorant Geometry.b1708 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1708 3 (by decide +kernel) x hx hd ho).elim

theorem bound1707 : BoxMajorant Geometry.b1707 := by
  exact PositiveLeaves.L1135.bound

theorem bound1202 : BoxMajorant Geometry.b1202 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1202.Widths)
  · have he : Geometry.b1202.half 2 false=Geometry.b1707 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1707
  · have he : Geometry.b1202.half 2 true=Geometry.b1708 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1708

theorem bound1201 : BoxMajorant Geometry.b1201 := by
  exact PositiveLeaves.L1136.bound

theorem bound873 : BoxMajorant Geometry.b873 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b873.Widths)
  · have he : Geometry.b873.half 1 false=Geometry.b1201 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1201
  · have he : Geometry.b873.half 1 true=Geometry.b1202 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1202

end N7.Kernel.Cover
