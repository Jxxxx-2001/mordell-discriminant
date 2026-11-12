import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.PositiveGroups.G0172
import N7.Kernel.PositiveGroups.G0173
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2076 : BoxMajorant Geometry.b2076 := by
  exact PositiveLeaves.L44.bound

theorem bound2075 : BoxMajorant Geometry.b2075 := by
  exact PositiveLeaves.L45.bound

theorem bound2074 : BoxMajorant Geometry.b2074 := by
  exact PositiveLeaves.L46.bound

theorem bound2073 : BoxMajorant Geometry.b2073 := by
  exact PositiveLeaves.L47.bound

theorem bound1428 : BoxMajorant Geometry.b1428 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1428.Widths)
  · have he : Geometry.b1428.half 2 false=Geometry.b2075 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2075
  · have he : Geometry.b1428.half 2 true=Geometry.b2076 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2076

theorem bound1427 : BoxMajorant Geometry.b1427 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1427.Widths)
  · have he : Geometry.b1427.half 2 false=Geometry.b2073 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2073
  · have he : Geometry.b1427.half 2 true=Geometry.b2074 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2074

theorem bound1017 : BoxMajorant Geometry.b1017 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1017.Widths)
  · have he : Geometry.b1017.half 1 false=Geometry.b1427 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1427
  · have he : Geometry.b1017.half 1 true=Geometry.b1428 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1428

end N7.Kernel.Cover
