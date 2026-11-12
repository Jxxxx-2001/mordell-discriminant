import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0138
import N7.Kernel.PositiveGroups.G0139
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2056 : BoxMajorant Geometry.b2056 := by
  exact PositiveLeaves.L110.bound

theorem bound2055 : BoxMajorant Geometry.b2055 := by
  exact PositiveLeaves.L111.bound

theorem bound1412 : BoxMajorant Geometry.b1412 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1412.Widths)
  · have he : Geometry.b1412.half 2 false=Geometry.b2055 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2055
  · have he : Geometry.b1412.half 2 true=Geometry.b2056 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2056

theorem bound1411 : BoxMajorant Geometry.b1411 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1411 0 (by decide +kernel) x hx hd ho).elim

theorem bound1004 : BoxMajorant Geometry.b1004 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1004 0 (by decide +kernel) x hx hd ho).elim

theorem bound1003 : BoxMajorant Geometry.b1003 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1003.Widths)
  · have he : Geometry.b1003.half 1 false=Geometry.b1411 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1411
  · have he : Geometry.b1003.half 1 true=Geometry.b1412 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1412

theorem bound700 : BoxMajorant Geometry.b700 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b700.Widths)
  · have he : Geometry.b700.half 0 false=Geometry.b1003 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1003
  · have he : Geometry.b700.half 0 true=Geometry.b1004 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1004

end N7.Kernel.Cover
