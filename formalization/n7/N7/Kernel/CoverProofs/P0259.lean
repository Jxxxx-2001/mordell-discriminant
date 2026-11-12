import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.PositiveGroups.G0287
import N7.Kernel.PositiveGroups.G0337
import N7.Kernel.PositiveGroups.G0366
import N7.Kernel.PositiveGroups.G0367
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4364 : BoxMajorant Geometry.b4364 := by
  exact PositiveLeaves.L1593.bound

theorem bound4363 : BoxMajorant Geometry.b4363 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4363 2 (by decide +kernel) x hx hd ho).elim

theorem bound4014 : BoxMajorant Geometry.b4014 := by
  exact PositiveLeaves.L1591.bound

theorem bound4013 : BoxMajorant Geometry.b4013 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4013 2 (by decide +kernel) x hx hd ho).elim

theorem bound4012 : BoxMajorant Geometry.b4012 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4012.Widths)
  · have he : Geometry.b4012.half 0 false=Geometry.b4363 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4363
  · have he : Geometry.b4012.half 0 true=Geometry.b4364 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4364

theorem bound4011 : BoxMajorant Geometry.b4011 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4011 2 (by decide +kernel) x hx hd ho).elim

theorem bound3636 : BoxMajorant Geometry.b3636 := by
  exact PositiveLeaves.L1590.bound

theorem bound3635 : BoxMajorant Geometry.b3635 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3635.Widths)
  · have he : Geometry.b3635.half 2 false=Geometry.b4013 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4013
  · have he : Geometry.b3635.half 2 true=Geometry.b4014 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4014

theorem bound3634 : BoxMajorant Geometry.b3634 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3634.Widths)
  · have he : Geometry.b3634.half 2 false=Geometry.b4011 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4011
  · have he : Geometry.b3634.half 2 true=Geometry.b4012 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4012

theorem bound3633 : BoxMajorant Geometry.b3633 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3633 2 (by decide +kernel) x hx hd ho).elim

theorem bound3360 : BoxMajorant Geometry.b3360 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3360.Widths)
  · have he : Geometry.b3360.half 1 false=Geometry.b3635 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3635
  · have he : Geometry.b3360.half 1 true=Geometry.b3636 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3636

theorem bound3359 : BoxMajorant Geometry.b3359 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3359.Widths)
  · have he : Geometry.b3359.half 1 false=Geometry.b3633 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3633
  · have he : Geometry.b3359.half 1 true=Geometry.b3634 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3634

theorem bound3016 : BoxMajorant Geometry.b3016 := by
  exact PositiveLeaves.L1589.bound

theorem bound3015 : BoxMajorant Geometry.b3015 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3015.Widths)
  · have he : Geometry.b3015.half 0 false=Geometry.b3359 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3359
  · have he : Geometry.b3015.half 0 true=Geometry.b3360 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3360

theorem bound2622 : BoxMajorant Geometry.b2622 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2622.Widths)
  · have he : Geometry.b2622.half 2 false=Geometry.b3015 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3015
  · have he : Geometry.b2622.half 2 true=Geometry.b3016 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3016

end N7.Kernel.Cover
