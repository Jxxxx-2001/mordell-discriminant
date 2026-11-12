import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverProofs.P0211
import N7.Kernel.PositiveGroups.G0065
import N7.Kernel.PositiveGroups.G0100
import N7.Kernel.PositiveGroups.G0141
import N7.Kernel.PositiveGroups.G0142
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3516 : BoxMajorant Geometry.b3516 := by
  exact PositiveLeaves.L2286.bound

theorem bound3240 : BoxMajorant Geometry.b3240 := by
  exact PositiveLeaves.L2281.bound

theorem bound3239 : BoxMajorant Geometry.b3239 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3239 2 (by decide +kernel) x hx hd ho).elim

theorem bound3238 : BoxMajorant Geometry.b3238 := by
  exact PositiveLeaves.L2283.bound

theorem bound3237 : BoxMajorant Geometry.b3237 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3237 2 (by decide +kernel) x hx hd ho).elim

theorem bound3236 : BoxMajorant Geometry.b3236 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3236.Widths)
  · have he : Geometry.b3236.half 1 false=Geometry.b3515 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3515
  · have he : Geometry.b3236.half 1 true=Geometry.b3516 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3516

theorem bound3235 : BoxMajorant Geometry.b3235 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3235 2 (by decide +kernel) x hx hd ho).elim

theorem bound2908 : BoxMajorant Geometry.b2908 := by
  exact PositiveLeaves.L2276.bound

theorem bound2907 : BoxMajorant Geometry.b2907 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2907 2 (by decide +kernel) x hx hd ho).elim

theorem bound2906 : BoxMajorant Geometry.b2906 := by
  exact PositiveLeaves.L2280.bound

theorem bound2905 : BoxMajorant Geometry.b2905 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2905.Widths)
  · have he : Geometry.b2905.half 0 false=Geometry.b3239 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3239
  · have he : Geometry.b2905.half 0 true=Geometry.b3240 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3240

theorem bound2904 : BoxMajorant Geometry.b2904 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2904.Widths)
  · have he : Geometry.b2904.half 0 false=Geometry.b3237 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3237
  · have he : Geometry.b2904.half 0 true=Geometry.b3238 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3238

theorem bound2903 : BoxMajorant Geometry.b2903 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2903 2 (by decide +kernel) x hx hd ho).elim

theorem bound2902 : BoxMajorant Geometry.b2902 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2902.Widths)
  · have he : Geometry.b2902.half 0 false=Geometry.b3235 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3235
  · have he : Geometry.b2902.half 0 true=Geometry.b3236 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3236

theorem bound2901 : BoxMajorant Geometry.b2901 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2901 2 (by decide +kernel) x hx hd ho).elim

theorem bound2560 : BoxMajorant Geometry.b2560 := by
  exact PositiveLeaves.L2275.bound

theorem bound2559 : BoxMajorant Geometry.b2559 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2559.Widths)
  · have he : Geometry.b2559.half 2 false=Geometry.b2907 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2907
  · have he : Geometry.b2559.half 2 true=Geometry.b2908 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2908

theorem bound2558 : BoxMajorant Geometry.b2558 := by
  exact PositiveLeaves.L2279.bound

theorem bound2557 : BoxMajorant Geometry.b2557 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2557.Widths)
  · have he : Geometry.b2557.half 2 false=Geometry.b2905 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2905
  · have he : Geometry.b2557.half 2 true=Geometry.b2906 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2906

theorem bound2556 : BoxMajorant Geometry.b2556 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2556.Widths)
  · have he : Geometry.b2556.half 2 false=Geometry.b2903 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2903
  · have he : Geometry.b2556.half 2 true=Geometry.b2904 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2904

theorem bound2555 : BoxMajorant Geometry.b2555 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2555.Widths)
  · have he : Geometry.b2555.half 2 false=Geometry.b2901 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2901
  · have he : Geometry.b2555.half 2 true=Geometry.b2902 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2902

theorem bound2198 : BoxMajorant Geometry.b2198 := by
  exact PositiveLeaves.L2274.bound

theorem bound2197 : BoxMajorant Geometry.b2197 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2197.Widths)
  · have he : Geometry.b2197.half 1 false=Geometry.b2559 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2559
  · have he : Geometry.b2197.half 1 true=Geometry.b2560 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2560

theorem bound2196 : BoxMajorant Geometry.b2196 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2196.Widths)
  · have he : Geometry.b2196.half 1 false=Geometry.b2557 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2557
  · have he : Geometry.b2196.half 1 true=Geometry.b2558 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2558

theorem bound2195 : BoxMajorant Geometry.b2195 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2195.Widths)
  · have he : Geometry.b2195.half 1 false=Geometry.b2555 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2555
  · have he : Geometry.b2195.half 1 true=Geometry.b2556 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2556

theorem bound1578 : BoxMajorant Geometry.b1578 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1578.Widths)
  · have he : Geometry.b1578.half 0 false=Geometry.b2197 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2197
  · have he : Geometry.b1578.half 0 true=Geometry.b2198 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2198

theorem bound1577 : BoxMajorant Geometry.b1577 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1577 2 (by decide +kernel) x hx hd ho).elim

theorem bound1576 : BoxMajorant Geometry.b1576 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1576.Widths)
  · have he : Geometry.b1576.half 0 false=Geometry.b2195 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2195
  · have he : Geometry.b1576.half 0 true=Geometry.b2196 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2196

theorem bound1575 : BoxMajorant Geometry.b1575 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1575 2 (by decide +kernel) x hx hd ho).elim

theorem bound1120 : BoxMajorant Geometry.b1120 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1120.Widths)
  · have he : Geometry.b1120.half 2 false=Geometry.b1577 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1577
  · have he : Geometry.b1120.half 2 true=Geometry.b1578 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1578

theorem bound1119 : BoxMajorant Geometry.b1119 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1119.Widths)
  · have he : Geometry.b1119.half 2 false=Geometry.b1575 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1575
  · have he : Geometry.b1119.half 2 true=Geometry.b1576 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1576

theorem bound811 : BoxMajorant Geometry.b811 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b811.Widths)
  · have he : Geometry.b811.half 1 false=Geometry.b1119 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1119
  · have he : Geometry.b811.half 1 true=Geometry.b1120 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1120

end N7.Kernel.Cover
