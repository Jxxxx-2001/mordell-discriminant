import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.PositiveGroups.G0289
import N7.Kernel.PositiveGroups.G0343
import N7.Kernel.PositiveGroups.G0344
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3932 : BoxMajorant Geometry.b3932 := by
  exact PositiveLeaves.L1854.bound

theorem bound3931 : BoxMajorant Geometry.b3931 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3931 2 (by decide +kernel) x hx hd ho).elim

theorem bound3930 : BoxMajorant Geometry.b3930 := by
  exact PositiveLeaves.L1856.bound

theorem bound3929 : BoxMajorant Geometry.b3929 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3929 2 (by decide +kernel) x hx hd ho).elim

theorem bound3586 : BoxMajorant Geometry.b3586 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3586.Widths)
  · have he : Geometry.b3586.half 2 false=Geometry.b3931 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3931
  · have he : Geometry.b3586.half 2 true=Geometry.b3932 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3932

theorem bound3585 : BoxMajorant Geometry.b3585 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3585.Widths)
  · have he : Geometry.b3585.half 2 false=Geometry.b3929 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3929
  · have he : Geometry.b3585.half 2 true=Geometry.b3930 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3930

theorem bound3316 : BoxMajorant Geometry.b3316 := by
  exact PositiveLeaves.L1853.bound

theorem bound3315 : BoxMajorant Geometry.b3315 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3315.Widths)
  · have he : Geometry.b3315.half 1 false=Geometry.b3585 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3585
  · have he : Geometry.b3315.half 1 true=Geometry.b3586 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3586

theorem bound2980 : BoxMajorant Geometry.b2980 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2980.Widths)
  · have he : Geometry.b2980.half 0 false=Geometry.b3315 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3315
  · have he : Geometry.b2980.half 0 true=Geometry.b3316 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3316

theorem bound2979 : BoxMajorant Geometry.b2979 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2979 2 (by decide +kernel) x hx hd ho).elim

theorem bound2604 : BoxMajorant Geometry.b2604 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2604.Widths)
  · have he : Geometry.b2604.half 2 false=Geometry.b2979 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2979
  · have he : Geometry.b2604.half 2 true=Geometry.b2980 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2980

end N7.Kernel.Cover
