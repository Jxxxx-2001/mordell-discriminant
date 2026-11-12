import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.PositiveGroups.G0471
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5880 : BoxMajorant Geometry.b5880 := by
  exact PositiveLeaves.L1275.bound

theorem bound5879 : BoxMajorant Geometry.b5879 := by
  exact PositiveLeaves.L1276.bound

theorem bound5842 : BoxMajorant Geometry.b5842 := by
  exact PositiveLeaves.L1274.bound

theorem bound5841 : BoxMajorant Geometry.b5841 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5841.Widths)
  · have he : Geometry.b5841.half 2 false=Geometry.b5879 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5879
  · have he : Geometry.b5841.half 2 true=Geometry.b5880 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5880

theorem bound5810 : BoxMajorant Geometry.b5810 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5810.Widths)
  · have he : Geometry.b5810.half 1 false=Geometry.b5841 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5841
  · have he : Geometry.b5810.half 1 true=Geometry.b5842 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5842

end N7.Kernel.Cover
