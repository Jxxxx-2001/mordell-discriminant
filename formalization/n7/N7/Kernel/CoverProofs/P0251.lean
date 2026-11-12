import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.PositiveGroups.G0340
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4894 : BoxMajorant Geometry.b4894 := by
  exact PositiveLeaves.L1817.bound

theorem bound4893 : BoxMajorant Geometry.b4893 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4893 2 (by decide +kernel) x hx hd ho).elim

theorem bound4568 : BoxMajorant Geometry.b4568 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4568.Widths)
  · have he : Geometry.b4568.half 2 false=Geometry.b4893 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4893
  · have he : Geometry.b4568.half 2 true=Geometry.b4894 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4894

theorem bound4567 : BoxMajorant Geometry.b4567 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4567 2 (by decide +kernel) x hx hd ho).elim

theorem bound4296 : BoxMajorant Geometry.b4296 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4296.Widths)
  · have he : Geometry.b4296.half 1 false=Geometry.b4567 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4567
  · have he : Geometry.b4296.half 1 true=Geometry.b4568 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4568

theorem bound4295 : BoxMajorant Geometry.b4295 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4295 2 (by decide +kernel) x hx hd ho).elim

theorem bound3942 : BoxMajorant Geometry.b3942 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3942.Widths)
  · have he : Geometry.b3942.half 0 false=Geometry.b4295 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4295
  · have he : Geometry.b3942.half 0 true=Geometry.b4296 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4296

theorem bound3941 : BoxMajorant Geometry.b3941 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3941 2 (by decide +kernel) x hx hd ho).elim

theorem bound3592 : BoxMajorant Geometry.b3592 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3592.Widths)
  · have he : Geometry.b3592.half 2 false=Geometry.b3941 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3941
  · have he : Geometry.b3592.half 2 true=Geometry.b3942 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3942

end N7.Kernel.Cover
