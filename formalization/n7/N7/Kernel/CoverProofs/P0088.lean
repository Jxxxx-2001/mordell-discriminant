import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.PositiveGroups.G0077
import N7.Kernel.PositiveGroups.G0115
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3668 : BoxMajorant Geometry.b3668 := by
  exact PositiveLeaves.L1203.bound

theorem bound3667 : BoxMajorant Geometry.b3667 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3667 0 (by decide +kernel) x hx hd ho).elim

theorem bound3404 : BoxMajorant Geometry.b3404 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3404 0 (by decide +kernel) x hx hd ho).elim

theorem bound3403 : BoxMajorant Geometry.b3403 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3403.Widths)
  · have he : Geometry.b3403.half 1 false=Geometry.b3667 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3667
  · have he : Geometry.b3403.half 1 true=Geometry.b3668 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3668

theorem bound3070 : BoxMajorant Geometry.b3070 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3070.Widths)
  · have he : Geometry.b3070.half 0 false=Geometry.b3403 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3403
  · have he : Geometry.b3070.half 0 true=Geometry.b3404 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3404

theorem bound3069 : BoxMajorant Geometry.b3069 := by
  exact PositiveLeaves.L1205.bound

theorem bound2666 : BoxMajorant Geometry.b2666 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2666.Widths)
  · have he : Geometry.b2666.half 2 false=Geometry.b3069 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3069
  · have he : Geometry.b2666.half 2 true=Geometry.b3070 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3070

theorem bound2665 : BoxMajorant Geometry.b2665 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2665 0 (by decide +kernel) x hx hd ho).elim

theorem bound2294 : BoxMajorant Geometry.b2294 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2294 0 (by decide +kernel) x hx hd ho).elim

theorem bound2293 : BoxMajorant Geometry.b2293 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2293.Widths)
  · have he : Geometry.b2293.half 1 false=Geometry.b2665 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2665
  · have he : Geometry.b2293.half 1 true=Geometry.b2666 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2666

theorem bound1672 : BoxMajorant Geometry.b1672 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1672.Widths)
  · have he : Geometry.b1672.half 0 false=Geometry.b2293 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2293
  · have he : Geometry.b1672.half 0 true=Geometry.b2294 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2294

end N7.Kernel.Cover
