import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.PositiveGroups.G0481
import N7.Kernel.PositiveGroups.G0482
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5642 : BoxMajorant Geometry.b5642 := by
  exact PositiveLeaves.L420.bound

theorem bound5641 : BoxMajorant Geometry.b5641 := by
  exact PositiveLeaves.L421.bound

theorem bound5640 : BoxMajorant Geometry.b5640 := by
  exact PositiveLeaves.L422.bound

theorem bound5639 : BoxMajorant Geometry.b5639 := by
  exact PositiveLeaves.L423.bound

theorem bound5604 : BoxMajorant Geometry.b5604 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5604.Widths)
  · have he : Geometry.b5604.half 2 false=Geometry.b5641 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5641
  · have he : Geometry.b5604.half 2 true=Geometry.b5642 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5642

theorem bound5603 : BoxMajorant Geometry.b5603 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5603.Widths)
  · have he : Geometry.b5603.half 2 false=Geometry.b5639 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5639
  · have he : Geometry.b5603.half 2 true=Geometry.b5640 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5640

theorem bound5576 : BoxMajorant Geometry.b5576 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5576.Widths)
  · have he : Geometry.b5576.half 1 false=Geometry.b5603 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5603
  · have he : Geometry.b5576.half 1 true=Geometry.b5604 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5604

end N7.Kernel.Cover
