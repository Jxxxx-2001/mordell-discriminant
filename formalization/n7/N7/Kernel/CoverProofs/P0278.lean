import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0333
import N7.Kernel.PositiveGroups.G0364
import N7.Kernel.PositiveGroups.G0395
import N7.Kernel.PositiveGroups.G0396
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5246 : BoxMajorant Geometry.b5246 := by
  exact PositiveLeaves.L1466.bound

theorem bound5245 : BoxMajorant Geometry.b5245 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5245 2 (by decide +kernel) x hx hd ho).elim

theorem bound5026 : BoxMajorant Geometry.b5026 := by
  exact PositiveLeaves.L1465.bound

theorem bound5025 : BoxMajorant Geometry.b5025 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5025.Widths)
  · have he : Geometry.b5025.half 0 false=Geometry.b5245 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5245
  · have he : Geometry.b5025.half 0 true=Geometry.b5246 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5246

theorem bound4656 : BoxMajorant Geometry.b4656 := by
  exact PositiveLeaves.L1464.bound

theorem bound4655 : BoxMajorant Geometry.b4655 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4655.Widths)
  · have he : Geometry.b4655.half 2 false=Geometry.b5025 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5025
  · have he : Geometry.b4655.half 2 true=Geometry.b5026 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5026

theorem bound4394 : BoxMajorant Geometry.b4394 := by
  exact PositiveLeaves.L1463.bound

theorem bound4393 : BoxMajorant Geometry.b4393 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4393.Widths)
  · have he : Geometry.b4393.half 1 false=Geometry.b4655 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4655
  · have he : Geometry.b4393.half 1 true=Geometry.b4656 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4656

theorem bound4044 : BoxMajorant Geometry.b4044 := by
  exact PositiveLeaves.L1462.bound

theorem bound4043 : BoxMajorant Geometry.b4043 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4043.Widths)
  · have he : Geometry.b4043.half 0 false=Geometry.b4393 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4393
  · have he : Geometry.b4043.half 0 true=Geometry.b4394 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4394

theorem bound3652 : BoxMajorant Geometry.b3652 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3652.Widths)
  · have he : Geometry.b3652.half 2 false=Geometry.b4043 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4043
  · have he : Geometry.b3652.half 2 true=Geometry.b4044 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4044

end N7.Kernel.Cover
