import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.PositiveGroups.G0102
import N7.Kernel.PositiveGroups.G0179
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2886 : BoxMajorant Geometry.b2886 := by
  exact PositiveLeaves.L2341.bound

theorem bound2885 : BoxMajorant Geometry.b2885 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2885 2 (by decide +kernel) x hx hd ho).elim

theorem bound2540 : BoxMajorant Geometry.b2540 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2540.Widths)
  · have he : Geometry.b2540.half 2 false=Geometry.b2885 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2885
  · have he : Geometry.b2540.half 2 true=Geometry.b2886 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2886

theorem bound2539 : BoxMajorant Geometry.b2539 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2539 2 (by decide +kernel) x hx hd ho).elim

theorem bound2180 : BoxMajorant Geometry.b2180 := by
  exact PositiveLeaves.L2340.bound

theorem bound2179 : BoxMajorant Geometry.b2179 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2179.Widths)
  · have he : Geometry.b2179.half 1 false=Geometry.b2539 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2539
  · have he : Geometry.b2179.half 1 true=Geometry.b2540 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2540

theorem bound1556 : BoxMajorant Geometry.b1556 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1556.Widths)
  · have he : Geometry.b1556.half 0 false=Geometry.b2179 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2179
  · have he : Geometry.b1556.half 0 true=Geometry.b2180 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2180

theorem bound1555 : BoxMajorant Geometry.b1555 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1555 2 (by decide +kernel) x hx hd ho).elim

theorem bound1108 : BoxMajorant Geometry.b1108 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1108.Widths)
  · have he : Geometry.b1108.half 2 false=Geometry.b1555 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1555
  · have he : Geometry.b1108.half 2 true=Geometry.b1556 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1556

theorem bound1107 : BoxMajorant Geometry.b1107 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1107 2 (by decide +kernel) x hx hd ho).elim

theorem bound805 : BoxMajorant Geometry.b805 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b805.Widths)
  · have he : Geometry.b805.half 1 false=Geometry.b1107 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1107
  · have he : Geometry.b805.half 1 true=Geometry.b1108 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1108

end N7.Kernel.Cover
