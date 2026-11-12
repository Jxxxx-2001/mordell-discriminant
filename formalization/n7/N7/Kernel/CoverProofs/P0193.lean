import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.PositiveGroups.G0231
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4444 : BoxMajorant Geometry.b4444 := by
  exact PositiveLeaves.L2904.bound

theorem bound4443 : BoxMajorant Geometry.b4443 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4443 2 (by decide +kernel) x hx hd ho).elim

theorem bound4152 : BoxMajorant Geometry.b4152 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4152.Widths)
  · have he : Geometry.b4152.half 1 false=Geometry.b4443 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4443
  · have he : Geometry.b4152.half 1 true=Geometry.b4444 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4444

theorem bound4151 : BoxMajorant Geometry.b4151 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4151 2 (by decide +kernel) x hx hd ho).elim

theorem bound3732 : BoxMajorant Geometry.b3732 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3732.Widths)
  · have he : Geometry.b3732.half 0 false=Geometry.b4151 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4151
  · have he : Geometry.b3732.half 0 true=Geometry.b4152 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4152

theorem bound3731 : BoxMajorant Geometry.b3731 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3731 2 (by decide +kernel) x hx hd ho).elim

theorem bound3456 : BoxMajorant Geometry.b3456 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3456.Widths)
  · have he : Geometry.b3456.half 2 false=Geometry.b3731 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3731
  · have he : Geometry.b3456.half 2 true=Geometry.b3732 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3732

theorem bound3455 : BoxMajorant Geometry.b3455 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3455 2 (by decide +kernel) x hx hd ho).elim

theorem bound3184 : BoxMajorant Geometry.b3184 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3184.Widths)
  · have he : Geometry.b3184.half 1 false=Geometry.b3455 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3455
  · have he : Geometry.b3184.half 1 true=Geometry.b3456 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3456

end N7.Kernel.Cover
