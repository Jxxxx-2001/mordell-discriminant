import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.PositiveGroups.G0320
import N7.Kernel.PositiveGroups.G0352
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3800 : BoxMajorant Geometry.b3800 := by
  exact PositiveLeaves.L2584.bound

theorem bound3799 : BoxMajorant Geometry.b3799 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3799 2 (by decide +kernel) x hx hd ho).elim

theorem bound3798 : BoxMajorant Geometry.b3798 := by
  exact PositiveLeaves.L2586.bound

theorem bound3797 : BoxMajorant Geometry.b3797 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3797 2 (by decide +kernel) x hx hd ho).elim

theorem bound3502 : BoxMajorant Geometry.b3502 := by
  exact PositiveLeaves.L2583.bound

theorem bound3501 : BoxMajorant Geometry.b3501 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3501.Widths)
  · have he : Geometry.b3501.half 2 false=Geometry.b3799 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3799
  · have he : Geometry.b3501.half 2 true=Geometry.b3800 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3800

theorem bound3500 : BoxMajorant Geometry.b3500 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3500.Widths)
  · have he : Geometry.b3500.half 2 false=Geometry.b3797 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3797
  · have he : Geometry.b3500.half 2 true=Geometry.b3798 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3798

theorem bound3499 : BoxMajorant Geometry.b3499 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3499 2 (by decide +kernel) x hx hd ho).elim

theorem bound3214 : BoxMajorant Geometry.b3214 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3214.Widths)
  · have he : Geometry.b3214.half 1 false=Geometry.b3501 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3501
  · have he : Geometry.b3214.half 1 true=Geometry.b3502 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3502

theorem bound3213 : BoxMajorant Geometry.b3213 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3213.Widths)
  · have he : Geometry.b3213.half 1 false=Geometry.b3499 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3499
  · have he : Geometry.b3213.half 1 true=Geometry.b3500 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3500

theorem bound2835 : BoxMajorant Geometry.b2835 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2835.Widths)
  · have he : Geometry.b2835.half 0 false=Geometry.b3213 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3213
  · have he : Geometry.b2835.half 0 true=Geometry.b3214 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3214

end N7.Kernel.Cover
