import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.PositiveGroups.G0294
import N7.Kernel.PositiveGroups.G0349
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3846 : BoxMajorant Geometry.b3846 := by
  exact PositiveLeaves.L2112.bound

theorem bound3845 : BoxMajorant Geometry.b3845 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3845 2 (by decide +kernel) x hx hd ho).elim

theorem bound3844 : BoxMajorant Geometry.b3844 := by
  exact PositiveLeaves.L2114.bound

theorem bound3843 : BoxMajorant Geometry.b3843 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3843 2 (by decide +kernel) x hx hd ho).elim

theorem bound3536 : BoxMajorant Geometry.b3536 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3536.Widths)
  · have he : Geometry.b3536.half 2 false=Geometry.b3845 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3845
  · have he : Geometry.b3536.half 2 true=Geometry.b3846 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3846

theorem bound3535 : BoxMajorant Geometry.b3535 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3535.Widths)
  · have he : Geometry.b3535.half 2 false=Geometry.b3843 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3843
  · have he : Geometry.b3535.half 2 true=Geometry.b3844 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3844

theorem bound3262 : BoxMajorant Geometry.b3262 := by
  exact PositiveLeaves.L2111.bound

theorem bound3261 : BoxMajorant Geometry.b3261 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3261.Widths)
  · have he : Geometry.b3261.half 1 false=Geometry.b3535 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3535
  · have he : Geometry.b3261.half 1 true=Geometry.b3536 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3536

theorem bound2934 : BoxMajorant Geometry.b2934 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2934.Widths)
  · have he : Geometry.b2934.half 0 false=Geometry.b3261 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3261
  · have he : Geometry.b2934.half 0 true=Geometry.b3262 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3262

end N7.Kernel.Cover
