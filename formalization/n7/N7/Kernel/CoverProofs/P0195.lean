import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.PositiveGroups.G0269
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3772 : BoxMajorant Geometry.b3772 := by
  exact PositiveLeaves.L2707.bound

theorem bound3771 : BoxMajorant Geometry.b3771 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3771 2 (by decide +kernel) x hx hd ho).elim

theorem bound3770 : BoxMajorant Geometry.b3770 := by
  exact PositiveLeaves.L2709.bound

theorem bound3769 : BoxMajorant Geometry.b3769 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3769 2 (by decide +kernel) x hx hd ho).elim

theorem bound3768 : BoxMajorant Geometry.b3768 := by
  exact PositiveLeaves.L2711.bound

theorem bound3767 : BoxMajorant Geometry.b3767 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3767 2 (by decide +kernel) x hx hd ho).elim

theorem bound3480 : BoxMajorant Geometry.b3480 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3480.Widths)
  · have he : Geometry.b3480.half 2 false=Geometry.b3771 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3771
  · have he : Geometry.b3480.half 2 true=Geometry.b3772 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3772

theorem bound3479 : BoxMajorant Geometry.b3479 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3479.Widths)
  · have he : Geometry.b3479.half 2 false=Geometry.b3769 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3769
  · have he : Geometry.b3479.half 2 true=Geometry.b3770 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3770

theorem bound3478 : BoxMajorant Geometry.b3478 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3478.Widths)
  · have he : Geometry.b3478.half 2 false=Geometry.b3767 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3767
  · have he : Geometry.b3478.half 2 true=Geometry.b3768 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3768

theorem bound3477 : BoxMajorant Geometry.b3477 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3477 2 (by decide +kernel) x hx hd ho).elim

theorem bound3200 : BoxMajorant Geometry.b3200 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3200.Widths)
  · have he : Geometry.b3200.half 1 false=Geometry.b3479 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3479
  · have he : Geometry.b3200.half 1 true=Geometry.b3480 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3480

theorem bound3199 : BoxMajorant Geometry.b3199 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3199.Widths)
  · have he : Geometry.b3199.half 1 false=Geometry.b3477 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3477
  · have he : Geometry.b3199.half 1 true=Geometry.b3478 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3478

theorem bound2817 : BoxMajorant Geometry.b2817 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2817.Widths)
  · have he : Geometry.b2817.half 0 false=Geometry.b3199 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3199
  · have he : Geometry.b2817.half 0 true=Geometry.b3200 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3200

end N7.Kernel.Cover
