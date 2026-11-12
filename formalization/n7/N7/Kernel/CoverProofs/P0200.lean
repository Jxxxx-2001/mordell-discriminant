import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.PositiveGroups.G0382
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4498 : BoxMajorant Geometry.b4498 := by
  exact PositiveLeaves.L2631.bound

theorem bound4497 : BoxMajorant Geometry.b4497 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4497 2 (by decide +kernel) x hx hd ho).elim

theorem bound4196 : BoxMajorant Geometry.b4196 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4196.Widths)
  · have he : Geometry.b4196.half 1 false=Geometry.b4497 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4497
  · have he : Geometry.b4196.half 1 true=Geometry.b4498 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4498

theorem bound4195 : BoxMajorant Geometry.b4195 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4195 2 (by decide +kernel) x hx hd ho).elim

theorem bound3790 : BoxMajorant Geometry.b3790 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3790.Widths)
  · have he : Geometry.b3790.half 0 false=Geometry.b4195 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4195
  · have he : Geometry.b3790.half 0 true=Geometry.b4196 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4196

theorem bound3789 : BoxMajorant Geometry.b3789 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3789 2 (by decide +kernel) x hx hd ho).elim

theorem bound3494 : BoxMajorant Geometry.b3494 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3494.Widths)
  · have he : Geometry.b3494.half 2 false=Geometry.b3789 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3789
  · have he : Geometry.b3494.half 2 true=Geometry.b3790 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3790

theorem bound3493 : BoxMajorant Geometry.b3493 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3493 2 (by decide +kernel) x hx hd ho).elim

theorem bound3210 : BoxMajorant Geometry.b3210 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3210.Widths)
  · have he : Geometry.b3210.half 1 false=Geometry.b3493 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3493
  · have he : Geometry.b3210.half 1 true=Geometry.b3494 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3494

theorem bound3209 : BoxMajorant Geometry.b3209 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3209 2 (by decide +kernel) x hx hd ho).elim

theorem bound2833 : BoxMajorant Geometry.b2833 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2833.Widths)
  · have he : Geometry.b2833.half 0 false=Geometry.b3209 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3209
  · have he : Geometry.b2833.half 0 true=Geometry.b3210 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3210

end N7.Kernel.Cover
