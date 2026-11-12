import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.PositiveGroups.G0147
import N7.Kernel.PositiveGroups.G0183
import N7.Kernel.PositiveGroups.G0228
import N7.Kernel.PositiveGroups.G0229
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4206 : BoxMajorant Geometry.b4206 := by
  exact PositiveLeaves.L2482.bound

theorem bound4205 : BoxMajorant Geometry.b4205 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4205 2 (by decide +kernel) x hx hd ho).elim

theorem bound3812 : BoxMajorant Geometry.b3812 := by
  exact PositiveLeaves.L2481.bound

theorem bound3811 : BoxMajorant Geometry.b3811 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3811.Widths)
  · have he : Geometry.b3811.half 0 false=Geometry.b4205 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4205
  · have he : Geometry.b3811.half 0 true=Geometry.b4206 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4206

theorem bound3512 : BoxMajorant Geometry.b3512 := by
  exact PositiveLeaves.L2480.bound

theorem bound3511 : BoxMajorant Geometry.b3511 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3511.Widths)
  · have he : Geometry.b3511.half 2 false=Geometry.b3811 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3811
  · have he : Geometry.b3511.half 2 true=Geometry.b3812 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3812

theorem bound3228 : BoxMajorant Geometry.b3228 := by
  exact PositiveLeaves.L2479.bound

theorem bound3227 : BoxMajorant Geometry.b3227 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3227.Widths)
  · have he : Geometry.b3227.half 1 false=Geometry.b3511 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3511
  · have he : Geometry.b3227.half 1 true=Geometry.b3512 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3512

theorem bound2865 : BoxMajorant Geometry.b2865 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2865.Widths)
  · have he : Geometry.b2865.half 0 false=Geometry.b3227 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3227
  · have he : Geometry.b2865.half 0 true=Geometry.b3228 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3228

end N7.Kernel.Cover
