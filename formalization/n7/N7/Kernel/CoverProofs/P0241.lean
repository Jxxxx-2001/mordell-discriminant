import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.PositiveGroups.G0290
import N7.Kernel.PositiveGroups.G0314
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3928 : BoxMajorant Geometry.b3928 := by
  exact PositiveLeaves.L1860.bound

theorem bound3927 : BoxMajorant Geometry.b3927 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3927 2 (by decide +kernel) x hx hd ho).elim

theorem bound3926 : BoxMajorant Geometry.b3926 := by
  exact PositiveLeaves.L1862.bound

theorem bound3925 : BoxMajorant Geometry.b3925 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3925 2 (by decide +kernel) x hx hd ho).elim

theorem bound3584 : BoxMajorant Geometry.b3584 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3584.Widths)
  · have he : Geometry.b3584.half 2 false=Geometry.b3927 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3927
  · have he : Geometry.b3584.half 2 true=Geometry.b3928 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3928

theorem bound3583 : BoxMajorant Geometry.b3583 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3583.Widths)
  · have he : Geometry.b3583.half 2 false=Geometry.b3925 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3925
  · have he : Geometry.b3583.half 2 true=Geometry.b3926 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3926

theorem bound3314 : BoxMajorant Geometry.b3314 := by
  exact PositiveLeaves.L1859.bound

theorem bound3313 : BoxMajorant Geometry.b3313 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3313.Widths)
  · have he : Geometry.b3313.half 1 false=Geometry.b3583 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3583
  · have he : Geometry.b3313.half 1 true=Geometry.b3584 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3584

theorem bound2978 : BoxMajorant Geometry.b2978 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2978.Widths)
  · have he : Geometry.b2978.half 0 false=Geometry.b3313 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3313
  · have he : Geometry.b2978.half 0 true=Geometry.b3314 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3314

theorem bound2977 : BoxMajorant Geometry.b2977 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2977 2 (by decide +kernel) x hx hd ho).elim

theorem bound2603 : BoxMajorant Geometry.b2603 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2603.Widths)
  · have he : Geometry.b2603.half 2 false=Geometry.b2977 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2977
  · have he : Geometry.b2603.half 2 true=Geometry.b2978 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2978

end N7.Kernel.Cover
