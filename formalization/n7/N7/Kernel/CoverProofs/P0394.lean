import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.PositiveGroups.G0444
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5072 : BoxMajorant Geometry.b5072 := by
  exact PositiveLeaves.L266.bound

theorem bound5071 : BoxMajorant Geometry.b5071 := by
  exact PositiveLeaves.L267.bound

theorem bound4692 : BoxMajorant Geometry.b4692 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4692.Widths)
  · have he : Geometry.b4692.half 2 false=Geometry.b5071 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5071
  · have he : Geometry.b4692.half 2 true=Geometry.b5072 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5072

end N7.Kernel.Cover
