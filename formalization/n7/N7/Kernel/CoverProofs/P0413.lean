import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.PositiveGroups.G0477
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5622 : BoxMajorant Geometry.b5622 := by
  exact PositiveLeaves.L291.bound

theorem bound5621 : BoxMajorant Geometry.b5621 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5621 0 (by decide +kernel) x hx hd ho).elim

theorem bound5587 : BoxMajorant Geometry.b5587 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5587.Widths)
  · have he : Geometry.b5587.half 1 false=Geometry.b5621 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5621
  · have he : Geometry.b5587.half 1 true=Geometry.b5622 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5622

end N7.Kernel.Cover
