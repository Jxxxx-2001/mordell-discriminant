import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.PositiveGroups.G0103
import N7.Kernel.PositiveGroups.G0144
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2266 : BoxMajorant Geometry.b2266 := by
  exact PositiveLeaves.L1409.bound

theorem bound2265 : BoxMajorant Geometry.b2265 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2265 2 (by decide +kernel) x hx hd ho).elim

theorem bound1650 : BoxMajorant Geometry.b1650 := by
  exact PositiveLeaves.L1408.bound

theorem bound1649 : BoxMajorant Geometry.b1649 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1649.Widths)
  · have he : Geometry.b1649.half 0 false=Geometry.b2265 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2265
  · have he : Geometry.b1649.half 0 true=Geometry.b2266 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2266

theorem bound1648 : BoxMajorant Geometry.b1648 := by
  exact PositiveLeaves.L1411.bound

theorem bound1647 : BoxMajorant Geometry.b1647 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1647 2 (by decide +kernel) x hx hd ho).elim

theorem bound1162 : BoxMajorant Geometry.b1162 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1162.Widths)
  · have he : Geometry.b1162.half 2 false=Geometry.b1649 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1649
  · have he : Geometry.b1162.half 2 true=Geometry.b1650 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1650

theorem bound1161 : BoxMajorant Geometry.b1161 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1161.Widths)
  · have he : Geometry.b1161.half 2 false=Geometry.b1647 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1647
  · have he : Geometry.b1161.half 2 true=Geometry.b1648 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1648

theorem bound843 : BoxMajorant Geometry.b843 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b843.Widths)
  · have he : Geometry.b843.half 1 false=Geometry.b1161 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1161
  · have he : Geometry.b843.half 1 true=Geometry.b1162 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1162

end N7.Kernel.Cover
