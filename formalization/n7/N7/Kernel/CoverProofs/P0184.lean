import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0131
import N7.Kernel.PositiveGroups.G0132
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2090 : BoxMajorant Geometry.b2090 := by
  exact PositiveLeaves.L17.bound

theorem bound2089 : BoxMajorant Geometry.b2089 := by
  exact PositiveLeaves.L18.bound

theorem bound1440 : BoxMajorant Geometry.b1440 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1440.Widths)
  · have he : Geometry.b1440.half 2 false=Geometry.b2089 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2089
  · have he : Geometry.b1440.half 2 true=Geometry.b2090 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2090

theorem bound1439 : BoxMajorant Geometry.b1439 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1439 0 (by decide +kernel) x hx hd ho).elim

theorem bound1023 : BoxMajorant Geometry.b1023 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1023.Widths)
  · have he : Geometry.b1023.half 1 false=Geometry.b1439 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1439
  · have he : Geometry.b1023.half 1 true=Geometry.b1440 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1440

end N7.Kernel.Cover
