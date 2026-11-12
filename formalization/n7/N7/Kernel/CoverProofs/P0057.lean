import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.PositiveGroups.G0019
import N7.Kernel.PositiveGroups.G0038
import N7.Kernel.PositiveGroups.G0039
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3814 : BoxMajorant Geometry.b3814 := by
  exact PositiveLeaves.L2307.bound

theorem bound3813 : BoxMajorant Geometry.b3813 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3813 2 (by decide +kernel) x hx hd ho).elim

theorem bound3514 : BoxMajorant Geometry.b3514 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3514.Widths)
  · have he : Geometry.b3514.half 2 false=Geometry.b3813 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3813
  · have he : Geometry.b3514.half 2 true=Geometry.b3814 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3814

theorem bound3513 : BoxMajorant Geometry.b3513 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3513 2 (by decide +kernel) x hx hd ho).elim

theorem bound3234 : BoxMajorant Geometry.b3234 := by
  exact PositiveLeaves.L2306.bound

theorem bound3233 : BoxMajorant Geometry.b3233 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3233.Widths)
  · have he : Geometry.b3233.half 1 false=Geometry.b3513 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3513
  · have he : Geometry.b3233.half 1 true=Geometry.b3514 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3514

theorem bound3232 : BoxMajorant Geometry.b3232 := by
  exact PositiveLeaves.L2313.bound

theorem bound3231 : BoxMajorant Geometry.b3231 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3231 2 (by decide +kernel) x hx hd ho).elim

theorem bound2894 : BoxMajorant Geometry.b2894 := by
  exact PositiveLeaves.L2304.bound

theorem bound2893 : BoxMajorant Geometry.b2893 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2893 2 (by decide +kernel) x hx hd ho).elim

theorem bound2892 : BoxMajorant Geometry.b2892 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2892.Widths)
  · have he : Geometry.b2892.half 0 false=Geometry.b3233 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3233
  · have he : Geometry.b2892.half 0 true=Geometry.b3234 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3234

theorem bound2891 : BoxMajorant Geometry.b2891 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2891 2 (by decide +kernel) x hx hd ho).elim

theorem bound2890 : BoxMajorant Geometry.b2890 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2890.Widths)
  · have he : Geometry.b2890.half 0 false=Geometry.b3231 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3231
  · have he : Geometry.b2890.half 0 true=Geometry.b3232 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3232

theorem bound2889 : BoxMajorant Geometry.b2889 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2889 2 (by decide +kernel) x hx hd ho).elim

theorem bound2550 : BoxMajorant Geometry.b2550 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2550.Widths)
  · have he : Geometry.b2550.half 2 false=Geometry.b2893 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2893
  · have he : Geometry.b2550.half 2 true=Geometry.b2894 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2894

theorem bound2549 : BoxMajorant Geometry.b2549 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2549.Widths)
  · have he : Geometry.b2549.half 2 false=Geometry.b2891 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2891
  · have he : Geometry.b2549.half 2 true=Geometry.b2892 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2892

theorem bound2548 : BoxMajorant Geometry.b2548 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2548.Widths)
  · have he : Geometry.b2548.half 2 false=Geometry.b2889 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2889
  · have he : Geometry.b2548.half 2 true=Geometry.b2890 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2890

theorem bound2547 : BoxMajorant Geometry.b2547 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2547 2 (by decide +kernel) x hx hd ho).elim

theorem bound2190 : BoxMajorant Geometry.b2190 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2190.Widths)
  · have he : Geometry.b2190.half 1 false=Geometry.b2549 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2549
  · have he : Geometry.b2190.half 1 true=Geometry.b2550 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2550

theorem bound2189 : BoxMajorant Geometry.b2189 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2189 2 (by decide +kernel) x hx hd ho).elim

theorem bound2188 : BoxMajorant Geometry.b2188 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2188.Widths)
  · have he : Geometry.b2188.half 1 false=Geometry.b2547 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2547
  · have he : Geometry.b2188.half 1 true=Geometry.b2548 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2548

theorem bound2187 : BoxMajorant Geometry.b2187 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2187 2 (by decide +kernel) x hx hd ho).elim

theorem bound1570 : BoxMajorant Geometry.b1570 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1570.Widths)
  · have he : Geometry.b1570.half 0 false=Geometry.b2189 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2189
  · have he : Geometry.b1570.half 0 true=Geometry.b2190 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2190

theorem bound1569 : BoxMajorant Geometry.b1569 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1569 2 (by decide +kernel) x hx hd ho).elim

theorem bound1568 : BoxMajorant Geometry.b1568 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1568.Widths)
  · have he : Geometry.b1568.half 0 false=Geometry.b2187 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2187
  · have he : Geometry.b1568.half 0 true=Geometry.b2188 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2188

theorem bound1567 : BoxMajorant Geometry.b1567 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1567 2 (by decide +kernel) x hx hd ho).elim

theorem bound1116 : BoxMajorant Geometry.b1116 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1116.Widths)
  · have he : Geometry.b1116.half 2 false=Geometry.b1569 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1569
  · have he : Geometry.b1116.half 2 true=Geometry.b1570 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1570

theorem bound1115 : BoxMajorant Geometry.b1115 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1115.Widths)
  · have he : Geometry.b1115.half 2 false=Geometry.b1567 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1567
  · have he : Geometry.b1115.half 2 true=Geometry.b1568 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1568

theorem bound809 : BoxMajorant Geometry.b809 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b809.Widths)
  · have he : Geometry.b809.half 1 false=Geometry.b1115 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1115
  · have he : Geometry.b809.half 1 true=Geometry.b1116 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1116

end N7.Kernel.Cover
