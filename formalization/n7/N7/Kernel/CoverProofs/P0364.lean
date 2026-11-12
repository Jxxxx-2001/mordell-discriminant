import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.PositiveGroups.G0404
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4866 : BoxMajorant Geometry.b4866 := by
  exact PositiveLeaves.L1964.bound

theorem bound4865 : BoxMajorant Geometry.b4865 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4865 2 (by decide +kernel) x hx hd ho).elim

theorem bound4549 : BoxMajorant Geometry.b4549 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4549.Widths)
  · have he : Geometry.b4549.half 2 false=Geometry.b4865 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4865
  · have he : Geometry.b4549.half 2 true=Geometry.b4866 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4866

end N7.Kernel.Cover
