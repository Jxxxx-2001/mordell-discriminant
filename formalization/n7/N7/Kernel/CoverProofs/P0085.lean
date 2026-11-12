import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.PositiveGroups.G0272
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4660 : BoxMajorant Geometry.b4660 := by
  exact PositiveLeaves.L1321.bound

theorem bound4659 : BoxMajorant Geometry.b4659 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4659 2 (by decide +kernel) x hx hd ho).elim

theorem bound4400 : BoxMajorant Geometry.b4400 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4400.Widths)
  · have he : Geometry.b4400.half 1 false=Geometry.b4659 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4659
  · have he : Geometry.b4400.half 1 true=Geometry.b4660 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4660

theorem bound4399 : BoxMajorant Geometry.b4399 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4399 2 (by decide +kernel) x hx hd ho).elim

theorem bound4058 : BoxMajorant Geometry.b4058 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4058.Widths)
  · have he : Geometry.b4058.half 0 false=Geometry.b4399 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4399
  · have he : Geometry.b4058.half 0 true=Geometry.b4400 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4400

theorem bound4057 : BoxMajorant Geometry.b4057 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4057 2 (by decide +kernel) x hx hd ho).elim

theorem bound3660 : BoxMajorant Geometry.b3660 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3660.Widths)
  · have he : Geometry.b3660.half 2 false=Geometry.b4057 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4057
  · have he : Geometry.b3660.half 2 true=Geometry.b4058 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4058

theorem bound3659 : BoxMajorant Geometry.b3659 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3659 2 (by decide +kernel) x hx hd ho).elim

theorem bound3394 : BoxMajorant Geometry.b3394 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3394.Widths)
  · have he : Geometry.b3394.half 1 false=Geometry.b3659 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3659
  · have he : Geometry.b3394.half 1 true=Geometry.b3660 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3660

theorem bound3393 : BoxMajorant Geometry.b3393 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3393 2 (by decide +kernel) x hx hd ho).elim

theorem bound3058 : BoxMajorant Geometry.b3058 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3058.Widths)
  · have he : Geometry.b3058.half 0 false=Geometry.b3393 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3393
  · have he : Geometry.b3058.half 0 true=Geometry.b3394 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3394

theorem bound3057 : BoxMajorant Geometry.b3057 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3057 2 (by decide +kernel) x hx hd ho).elim

theorem bound2650 : BoxMajorant Geometry.b2650 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2650.Widths)
  · have he : Geometry.b2650.half 2 false=Geometry.b3057 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3057
  · have he : Geometry.b2650.half 2 true=Geometry.b3058 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3058

end N7.Kernel.Cover
