import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.PositiveGroups.G0342
import N7.Kernel.PositiveGroups.G0343
import N7.Kernel.PositiveGroups.G0374
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4278 : BoxMajorant Geometry.b4278 := by
  exact PositiveLeaves.L1915.bound

theorem bound4277 : BoxMajorant Geometry.b4277 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4277 2 (by decide +kernel) x hx hd ho).elim

theorem bound4276 : BoxMajorant Geometry.b4276 := by
  exact PositiveLeaves.L1918.bound

theorem bound4275 : BoxMajorant Geometry.b4275 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4275 2 (by decide +kernel) x hx hd ho).elim

theorem bound4274 : BoxMajorant Geometry.b4274 := by
  exact PositiveLeaves.L1920.bound

theorem bound4273 : BoxMajorant Geometry.b4273 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4273 2 (by decide +kernel) x hx hd ho).elim

theorem bound4272 : BoxMajorant Geometry.b4272 := by
  exact PositiveLeaves.L1923.bound

theorem bound4271 : BoxMajorant Geometry.b4271 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4271 2 (by decide +kernel) x hx hd ho).elim

theorem bound3912 : BoxMajorant Geometry.b3912 := by
  exact PositiveLeaves.L1914.bound

theorem bound3911 : BoxMajorant Geometry.b3911 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3911.Widths)
  · have he : Geometry.b3911.half 0 false=Geometry.b4277 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4277
  · have he : Geometry.b3911.half 0 true=Geometry.b4278 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4278

theorem bound3910 : BoxMajorant Geometry.b3910 := by
  exact PositiveLeaves.L1917.bound

theorem bound3909 : BoxMajorant Geometry.b3909 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3909.Widths)
  · have he : Geometry.b3909.half 0 false=Geometry.b4275 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4275
  · have he : Geometry.b3909.half 0 true=Geometry.b4276 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4276

theorem bound3908 : BoxMajorant Geometry.b3908 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3908.Widths)
  · have he : Geometry.b3908.half 0 false=Geometry.b4273 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4273
  · have he : Geometry.b3908.half 0 true=Geometry.b4274 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4274

theorem bound3907 : BoxMajorant Geometry.b3907 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3907 2 (by decide +kernel) x hx hd ho).elim

theorem bound3906 : BoxMajorant Geometry.b3906 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3906.Widths)
  · have he : Geometry.b3906.half 0 false=Geometry.b4271 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4271
  · have he : Geometry.b3906.half 0 true=Geometry.b4272 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4272

theorem bound3905 : BoxMajorant Geometry.b3905 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3905 2 (by decide +kernel) x hx hd ho).elim

theorem bound3574 : BoxMajorant Geometry.b3574 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3574.Widths)
  · have he : Geometry.b3574.half 2 false=Geometry.b3911 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3911
  · have he : Geometry.b3574.half 2 true=Geometry.b3912 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3912

theorem bound3573 : BoxMajorant Geometry.b3573 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3573.Widths)
  · have he : Geometry.b3573.half 2 false=Geometry.b3909 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3909
  · have he : Geometry.b3573.half 2 true=Geometry.b3910 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3910

theorem bound3572 : BoxMajorant Geometry.b3572 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3572.Widths)
  · have he : Geometry.b3572.half 2 false=Geometry.b3907 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3907
  · have he : Geometry.b3572.half 2 true=Geometry.b3908 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3908

theorem bound3571 : BoxMajorant Geometry.b3571 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3571.Widths)
  · have he : Geometry.b3571.half 2 false=Geometry.b3905 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3905
  · have he : Geometry.b3571.half 2 true=Geometry.b3906 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3906

theorem bound3300 : BoxMajorant Geometry.b3300 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3300.Widths)
  · have he : Geometry.b3300.half 1 false=Geometry.b3573 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3573
  · have he : Geometry.b3300.half 1 true=Geometry.b3574 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3574

theorem bound3299 : BoxMajorant Geometry.b3299 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3299.Widths)
  · have he : Geometry.b3299.half 1 false=Geometry.b3571 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3571
  · have he : Geometry.b3299.half 1 true=Geometry.b3572 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3572

theorem bound2964 : BoxMajorant Geometry.b2964 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2964.Widths)
  · have he : Geometry.b2964.half 0 false=Geometry.b3299 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3299
  · have he : Geometry.b2964.half 0 true=Geometry.b3300 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3300

end N7.Kernel.Cover
