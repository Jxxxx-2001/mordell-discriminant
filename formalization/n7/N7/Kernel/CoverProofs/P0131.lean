import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.CoverGeometry.G0029
import N7.Kernel.PositiveGroups.G0082
import N7.Kernel.PositiveGroups.G0120
import N7.Kernel.PositiveGroups.G0160
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1856 : BoxMajorant Geometry.b1856 := by
  exact PositiveLeaves.L791.bound

theorem bound1855 : BoxMajorant Geometry.b1855 := by
  exact PositiveLeaves.L792.bound

theorem bound1854 : BoxMajorant Geometry.b1854 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1854 3 (by decide +kernel) x hx hd ho).elim

theorem bound1853 : BoxMajorant Geometry.b1853 := by
  exact PositiveLeaves.L795.bound

theorem bound1290 : BoxMajorant Geometry.b1290 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1290.Widths)
  · have he : Geometry.b1290.half 2 false=Geometry.b1855 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1855
  · have he : Geometry.b1290.half 2 true=Geometry.b1856 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1856

theorem bound1289 : BoxMajorant Geometry.b1289 := by
  exact PositiveLeaves.L793.bound

theorem bound1288 : BoxMajorant Geometry.b1288 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1288.Widths)
  · have he : Geometry.b1288.half 2 false=Geometry.b1853 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1853
  · have he : Geometry.b1288.half 2 true=Geometry.b1854 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1854

theorem bound1287 : BoxMajorant Geometry.b1287 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1287 3 (by decide +kernel) x hx hd ho).elim

theorem bound932 : BoxMajorant Geometry.b932 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b932.Widths)
  · have he : Geometry.b932.half 1 false=Geometry.b1289 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1289
  · have he : Geometry.b932.half 1 true=Geometry.b1290 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1290

theorem bound931 : BoxMajorant Geometry.b931 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b931.Widths)
  · have he : Geometry.b931.half 1 false=Geometry.b1287 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1287
  · have he : Geometry.b931.half 1 true=Geometry.b1288 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1288

theorem bound643 : BoxMajorant Geometry.b643 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b643.Widths)
  · have he : Geometry.b643.half 0 false=Geometry.b931 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound931
  · have he : Geometry.b643.half 0 true=Geometry.b932 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound932

end N7.Kernel.Cover
