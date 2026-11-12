import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.PositiveGroups.G0103
import N7.Kernel.PositiveGroups.G0143
import N7.Kernel.PositiveGroups.G0144
import N7.Kernel.PositiveGroups.G0180
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3048 : BoxMajorant Geometry.b3048 := by
  exact PositiveLeaves.L1397.bound

theorem bound3047 : BoxMajorant Geometry.b3047 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3047 2 (by decide +kernel) x hx hd ho).elim

theorem bound3046 : BoxMajorant Geometry.b3046 := by
  exact PositiveLeaves.L1399.bound

theorem bound3045 : BoxMajorant Geometry.b3045 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3045 2 (by decide +kernel) x hx hd ho).elim

theorem bound3044 : BoxMajorant Geometry.b3044 := by
  exact PositiveLeaves.L1403.bound

theorem bound3043 : BoxMajorant Geometry.b3043 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3043 2 (by decide +kernel) x hx hd ho).elim

theorem bound2642 : BoxMajorant Geometry.b2642 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2642.Widths)
  · have he : Geometry.b2642.half 2 false=Geometry.b3047 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3047
  · have he : Geometry.b2642.half 2 true=Geometry.b3048 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3048

theorem bound2641 : BoxMajorant Geometry.b2641 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2641.Widths)
  · have he : Geometry.b2641.half 2 false=Geometry.b3045 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3045
  · have he : Geometry.b2641.half 2 true=Geometry.b3046 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3046

theorem bound2640 : BoxMajorant Geometry.b2640 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2640.Widths)
  · have he : Geometry.b2640.half 2 false=Geometry.b3043 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3043
  · have he : Geometry.b2640.half 2 true=Geometry.b3044 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3044

theorem bound2639 : BoxMajorant Geometry.b2639 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2639 2 (by decide +kernel) x hx hd ho).elim

theorem bound2270 : BoxMajorant Geometry.b2270 := by
  exact PositiveLeaves.L1396.bound

theorem bound2269 : BoxMajorant Geometry.b2269 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2269.Widths)
  · have he : Geometry.b2269.half 1 false=Geometry.b2641 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2641
  · have he : Geometry.b2269.half 1 true=Geometry.b2642 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2642

theorem bound2268 : BoxMajorant Geometry.b2268 := by
  exact PositiveLeaves.L1402.bound

theorem bound2267 : BoxMajorant Geometry.b2267 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2267.Widths)
  · have he : Geometry.b2267.half 1 false=Geometry.b2639 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2639
  · have he : Geometry.b2267.half 1 true=Geometry.b2640 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2640

theorem bound1654 : BoxMajorant Geometry.b1654 := by
  exact PositiveLeaves.L1395.bound

theorem bound1653 : BoxMajorant Geometry.b1653 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1653.Widths)
  · have he : Geometry.b1653.half 0 false=Geometry.b2269 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2269
  · have he : Geometry.b1653.half 0 true=Geometry.b2270 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2270

theorem bound1652 : BoxMajorant Geometry.b1652 := by
  exact PositiveLeaves.L1401.bound

theorem bound1651 : BoxMajorant Geometry.b1651 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1651.Widths)
  · have he : Geometry.b1651.half 0 false=Geometry.b2267 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2267
  · have he : Geometry.b1651.half 0 true=Geometry.b2268 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2268

theorem bound1164 : BoxMajorant Geometry.b1164 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1164.Widths)
  · have he : Geometry.b1164.half 2 false=Geometry.b1653 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1653
  · have he : Geometry.b1164.half 2 true=Geometry.b1654 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1654

theorem bound1163 : BoxMajorant Geometry.b1163 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1163.Widths)
  · have he : Geometry.b1163.half 2 false=Geometry.b1651 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1651
  · have he : Geometry.b1163.half 2 true=Geometry.b1652 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1652

theorem bound845 : BoxMajorant Geometry.b845 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b845.Widths)
  · have he : Geometry.b845.half 1 false=Geometry.b1163 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1163
  · have he : Geometry.b845.half 1 true=Geometry.b1164 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1164

end N7.Kernel.Cover
