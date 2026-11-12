import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.PositiveGroups.G0156
import N7.Kernel.PositiveGroups.G0192
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3062 : BoxMajorant Geometry.b3062 := by
  exact PositiveLeaves.L1256.bound

theorem bound3061 : BoxMajorant Geometry.b3061 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3061 2 (by decide +kernel) x hx hd ho).elim

theorem bound2656 : BoxMajorant Geometry.b2656 := by
  exact PositiveLeaves.L1255.bound

theorem bound2655 : BoxMajorant Geometry.b2655 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2655.Widths)
  · have he : Geometry.b2655.half 2 false=Geometry.b3061 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3061
  · have he : Geometry.b2655.half 2 true=Geometry.b3062 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3062

theorem bound2282 : BoxMajorant Geometry.b2282 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2282.Widths)
  · have he : Geometry.b2282.half 1 false=Geometry.b2655 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2655
  · have he : Geometry.b2282.half 1 true=Geometry.b2656 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2656

end N7.Kernel.Cover
