import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.PositiveGroups.G0054
import N7.Kernel.PositiveGroups.G0084
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1278 : BoxMajorant Geometry.b1278 := by
  exact PositiveLeaves.L820.bound

theorem bound1277 : BoxMajorant Geometry.b1277 := by
  exact PositiveLeaves.L821.bound

theorem bound922 : BoxMajorant Geometry.b922 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b922.Widths)
  · have he : Geometry.b922.half 1 false=Geometry.b1277 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1277
  · have he : Geometry.b922.half 1 true=Geometry.b1278 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1278

theorem bound921 : BoxMajorant Geometry.b921 := by
  exact PositiveLeaves.L822.bound

theorem bound633 : BoxMajorant Geometry.b633 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b633.Widths)
  · have he : Geometry.b633.half 0 false=Geometry.b921 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound921
  · have he : Geometry.b633.half 0 true=Geometry.b922 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound922

end N7.Kernel.Cover
