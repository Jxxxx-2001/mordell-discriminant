import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.PositiveGroups.G0025
import N7.Kernel.PositiveGroups.G0046
import N7.Kernel.PositiveGroups.G0073
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1518 : BoxMajorant Geometry.b1518 := by
  exact PositiveLeaves.L2463.bound

theorem bound1517 : BoxMajorant Geometry.b1517 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1517 2 (by decide +kernel) x hx hd ho).elim

theorem bound1076 : BoxMajorant Geometry.b1076 := by
  exact PositiveLeaves.L2462.bound

theorem bound1075 : BoxMajorant Geometry.b1075 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1075.Widths)
  · have he : Geometry.b1075.half 2 false=Geometry.b1517 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1517
  · have he : Geometry.b1075.half 2 true=Geometry.b1518 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1518

theorem bound778 : BoxMajorant Geometry.b778 := by
  exact PositiveLeaves.L2461.bound

theorem bound777 : BoxMajorant Geometry.b777 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b777.Widths)
  · have he : Geometry.b777.half 1 false=Geometry.b1075 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1075
  · have he : Geometry.b777.half 1 true=Geometry.b1076 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1076

theorem bound499 : BoxMajorant Geometry.b499 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b499.Widths)
  · have he : Geometry.b499.half 0 false=Geometry.b777 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound777
  · have he : Geometry.b499.half 0 true=Geometry.b778 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound778

end N7.Kernel.Cover
