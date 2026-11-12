import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.PositiveGroups.G0299
import N7.Kernel.PositiveGroups.G0300
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3428 : BoxMajorant Geometry.b3428 := by
  exact PositiveLeaves.L632.bound

theorem bound3427 : BoxMajorant Geometry.b3427 := by
  exact PositiveLeaves.L633.bound

theorem bound3142 : BoxMajorant Geometry.b3142 := by
  exact PositiveLeaves.L631.bound

theorem bound3141 : BoxMajorant Geometry.b3141 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3141.Widths)
  · have he : Geometry.b3141.half 0 false=Geometry.b3427 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3427
  · have he : Geometry.b3141.half 0 true=Geometry.b3428 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3428

theorem bound2749 : BoxMajorant Geometry.b2749 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2749.Widths)
  · have he : Geometry.b2749.half 2 false=Geometry.b3141 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3141
  · have he : Geometry.b2749.half 2 true=Geometry.b3142 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3142

end N7.Kernel.Cover
