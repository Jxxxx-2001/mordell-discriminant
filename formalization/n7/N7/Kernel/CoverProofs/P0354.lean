import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.PositiveGroups.G0382
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4802 : BoxMajorant Geometry.b4802 := by
  exact PositiveLeaves.L2592.bound

theorem bound4801 : BoxMajorant Geometry.b4801 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4801 2 (by decide +kernel) x hx hd ho).elim

theorem bound4510 : BoxMajorant Geometry.b4510 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4510.Widths)
  · have he : Geometry.b4510.half 2 false=Geometry.b4801 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4801
  · have he : Geometry.b4510.half 2 true=Geometry.b4802 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4802

end N7.Kernel.Cover
