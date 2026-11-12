import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.PositiveGroups.G0479
import N7.Kernel.PositiveGroups.G0480
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5638 : BoxMajorant Geometry.b5638 := by
  exact PositiveLeaves.L429.bound

theorem bound5637 : BoxMajorant Geometry.b5637 := by
  exact PositiveLeaves.L430.bound

theorem bound5602 : BoxMajorant Geometry.b5602 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5602.Widths)
  · have he : Geometry.b5602.half 2 false=Geometry.b5637 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5637
  · have he : Geometry.b5602.half 2 true=Geometry.b5638 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5638

theorem bound5601 : BoxMajorant Geometry.b5601 := by
  exact PositiveLeaves.L431.bound

theorem bound5574 : BoxMajorant Geometry.b5574 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5574.Widths)
  · have he : Geometry.b5574.half 1 false=Geometry.b5601 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5601
  · have he : Geometry.b5574.half 1 true=Geometry.b5602 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5602

end N7.Kernel.Cover
