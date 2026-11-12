import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.PositiveGroups.G0142
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3816 : BoxMajorant Geometry.b3816 := by
  exact PositiveLeaves.L2287.bound

theorem bound3815 : BoxMajorant Geometry.b3815 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3815 2 (by decide +kernel) x hx hd ho).elim

theorem bound3515 : BoxMajorant Geometry.b3515 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3515.Widths)
  · have he : Geometry.b3515.half 2 false=Geometry.b3815 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3815
  · have he : Geometry.b3515.half 2 true=Geometry.b3816 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3816

end N7.Kernel.Cover
