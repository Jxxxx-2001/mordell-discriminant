import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0030
import N7.Kernel.PositiveGroups.G0118
import N7.Kernel.PositiveGroups.G0156
import N7.Kernel.PositiveGroups.G0195
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1954 : BoxMajorant Geometry.b1954 := by
  exact PositiveLeaves.L610.bound

theorem bound1953 : BoxMajorant Geometry.b1953 := by
  exact PositiveLeaves.L611.bound

theorem bound1346 : BoxMajorant Geometry.b1346 := by
  exact PositiveLeaves.L609.bound

theorem bound1345 : BoxMajorant Geometry.b1345 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1345.Widths)
  · have he : Geometry.b1345.half 2 false=Geometry.b1953 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1953
  · have he : Geometry.b1345.half 2 true=Geometry.b1954 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1954

theorem bound962 : BoxMajorant Geometry.b962 := by
  exact PositiveLeaves.L608.bound

theorem bound961 : BoxMajorant Geometry.b961 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b961.Widths)
  · have he : Geometry.b961.half 1 false=Geometry.b1345 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1345
  · have he : Geometry.b961.half 1 true=Geometry.b1346 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1346

theorem bound669 : BoxMajorant Geometry.b669 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b669.Widths)
  · have he : Geometry.b669.half 0 false=Geometry.b961 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound961
  · have he : Geometry.b669.half 0 true=Geometry.b962 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound962

end N7.Kernel.Cover
