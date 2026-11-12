import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.PositiveGroups.G0149
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2526 : BoxMajorant Geometry.b2526 := by
  exact PositiveLeaves.L2410.bound

theorem bound2525 : BoxMajorant Geometry.b2525 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2525 2 (by decide +kernel) x hx hd ho).elim

theorem bound2168 : BoxMajorant Geometry.b2168 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2168.Widths)
  · have he : Geometry.b2168.half 1 false=Geometry.b2525 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2525
  · have he : Geometry.b2168.half 1 true=Geometry.b2526 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2526

theorem bound2167 : BoxMajorant Geometry.b2167 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2167 2 (by decide +kernel) x hx hd ho).elim

theorem bound1534 : BoxMajorant Geometry.b1534 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1534.Widths)
  · have he : Geometry.b1534.half 0 false=Geometry.b2167 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2167
  · have he : Geometry.b1534.half 0 true=Geometry.b2168 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2168

theorem bound1533 : BoxMajorant Geometry.b1533 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1533 2 (by decide +kernel) x hx hd ho).elim

theorem bound1090 : BoxMajorant Geometry.b1090 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1090.Widths)
  · have he : Geometry.b1090.half 2 false=Geometry.b1533 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1533
  · have he : Geometry.b1090.half 2 true=Geometry.b1534 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1534

theorem bound1089 : BoxMajorant Geometry.b1089 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1089 2 (by decide +kernel) x hx hd ho).elim

theorem bound790 : BoxMajorant Geometry.b790 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b790.Widths)
  · have he : Geometry.b790.half 1 false=Geometry.b1089 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1089
  · have he : Geometry.b790.half 1 true=Geometry.b1090 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1090

theorem bound789 : BoxMajorant Geometry.b789 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b789 2 (by decide +kernel) x hx hd ho).elim

theorem bound509 : BoxMajorant Geometry.b509 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b509.Widths)
  · have he : Geometry.b509.half 0 false=Geometry.b789 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound789
  · have he : Geometry.b509.half 0 true=Geometry.b790 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound790

end N7.Kernel.Cover
