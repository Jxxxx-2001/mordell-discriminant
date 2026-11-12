import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.PositiveGroups.G0313
import N7.Kernel.PositiveGroups.G0341
import N7.Kernel.PositiveGroups.G0342
import N7.Kernel.PositiveGroups.G0372
import N7.Kernel.PositiveGroups.G0373
import N7.Kernel.PositiveGroups.G0374
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4882 : BoxMajorant Geometry.b4882 := by
  exact PositiveLeaves.L1892.bound

theorem bound4881 : BoxMajorant Geometry.b4881 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4881 2 (by decide +kernel) x hx hd ho).elim

theorem bound4880 : BoxMajorant Geometry.b4880 := by
  exact PositiveLeaves.L1894.bound

theorem bound4879 : BoxMajorant Geometry.b4879 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4879 2 (by decide +kernel) x hx hd ho).elim

theorem bound4878 : BoxMajorant Geometry.b4878 := by
  exact PositiveLeaves.L1898.bound

theorem bound4877 : BoxMajorant Geometry.b4877 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4877 2 (by decide +kernel) x hx hd ho).elim

theorem bound4876 : BoxMajorant Geometry.b4876 := by
  exact PositiveLeaves.L1900.bound

theorem bound4875 : BoxMajorant Geometry.b4875 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4875 2 (by decide +kernel) x hx hd ho).elim

theorem bound4874 : BoxMajorant Geometry.b4874 := by
  exact PositiveLeaves.L1903.bound

theorem bound4873 : BoxMajorant Geometry.b4873 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4873 2 (by decide +kernel) x hx hd ho).elim

theorem bound4872 : BoxMajorant Geometry.b4872 := by
  exact PositiveLeaves.L1905.bound

theorem bound4871 : BoxMajorant Geometry.b4871 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4871 2 (by decide +kernel) x hx hd ho).elim

theorem bound4870 : BoxMajorant Geometry.b4870 := by
  exact PositiveLeaves.L1909.bound

theorem bound4869 : BoxMajorant Geometry.b4869 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4869 2 (by decide +kernel) x hx hd ho).elim

theorem bound4560 : BoxMajorant Geometry.b4560 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4560.Widths)
  · have he : Geometry.b4560.half 2 false=Geometry.b4881 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4881
  · have he : Geometry.b4560.half 2 true=Geometry.b4882 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4882

theorem bound4559 : BoxMajorant Geometry.b4559 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4559.Widths)
  · have he : Geometry.b4559.half 2 false=Geometry.b4879 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4879
  · have he : Geometry.b4559.half 2 true=Geometry.b4880 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4880

theorem bound4558 : BoxMajorant Geometry.b4558 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4558.Widths)
  · have he : Geometry.b4558.half 2 false=Geometry.b4877 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4877
  · have he : Geometry.b4558.half 2 true=Geometry.b4878 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4878

theorem bound4557 : BoxMajorant Geometry.b4557 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4557.Widths)
  · have he : Geometry.b4557.half 2 false=Geometry.b4875 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4875
  · have he : Geometry.b4557.half 2 true=Geometry.b4876 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4876

theorem bound4556 : BoxMajorant Geometry.b4556 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4556.Widths)
  · have he : Geometry.b4556.half 2 false=Geometry.b4873 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4873
  · have he : Geometry.b4556.half 2 true=Geometry.b4874 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4874

theorem bound4555 : BoxMajorant Geometry.b4555 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4555.Widths)
  · have he : Geometry.b4555.half 2 false=Geometry.b4871 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4871
  · have he : Geometry.b4555.half 2 true=Geometry.b4872 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4872

theorem bound4554 : BoxMajorant Geometry.b4554 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4554.Widths)
  · have he : Geometry.b4554.half 2 false=Geometry.b4869 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4869
  · have he : Geometry.b4554.half 2 true=Geometry.b4870 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4870

theorem bound4553 : BoxMajorant Geometry.b4553 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4553 2 (by decide +kernel) x hx hd ho).elim

theorem bound4286 : BoxMajorant Geometry.b4286 := by
  exact PositiveLeaves.L1891.bound

theorem bound4285 : BoxMajorant Geometry.b4285 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4285.Widths)
  · have he : Geometry.b4285.half 1 false=Geometry.b4559 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4559
  · have he : Geometry.b4285.half 1 true=Geometry.b4560 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4560

theorem bound4284 : BoxMajorant Geometry.b4284 := by
  exact PositiveLeaves.L1897.bound

theorem bound4283 : BoxMajorant Geometry.b4283 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4283.Widths)
  · have he : Geometry.b4283.half 1 false=Geometry.b4557 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4557
  · have he : Geometry.b4283.half 1 true=Geometry.b4558 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4558

theorem bound4282 : BoxMajorant Geometry.b4282 := by
  exact PositiveLeaves.L1902.bound

theorem bound4281 : BoxMajorant Geometry.b4281 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4281.Widths)
  · have he : Geometry.b4281.half 1 false=Geometry.b4555 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4555
  · have he : Geometry.b4281.half 1 true=Geometry.b4556 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4556

theorem bound4280 : BoxMajorant Geometry.b4280 := by
  exact PositiveLeaves.L1908.bound

theorem bound4279 : BoxMajorant Geometry.b4279 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4279.Widths)
  · have he : Geometry.b4279.half 1 false=Geometry.b4553 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4553
  · have he : Geometry.b4279.half 1 true=Geometry.b4554 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4554

theorem bound3920 : BoxMajorant Geometry.b3920 := by
  exact PositiveLeaves.L1890.bound

theorem bound3919 : BoxMajorant Geometry.b3919 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3919.Widths)
  · have he : Geometry.b3919.half 0 false=Geometry.b4285 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4285
  · have he : Geometry.b3919.half 0 true=Geometry.b4286 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4286

theorem bound3918 : BoxMajorant Geometry.b3918 := by
  exact PositiveLeaves.L1896.bound

theorem bound3917 : BoxMajorant Geometry.b3917 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3917.Widths)
  · have he : Geometry.b3917.half 0 false=Geometry.b4283 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4283
  · have he : Geometry.b3917.half 0 true=Geometry.b4284 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4284

theorem bound3916 : BoxMajorant Geometry.b3916 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3916.Widths)
  · have he : Geometry.b3916.half 0 false=Geometry.b4281 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4281
  · have he : Geometry.b3916.half 0 true=Geometry.b4282 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4282

theorem bound3915 : BoxMajorant Geometry.b3915 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3915 2 (by decide +kernel) x hx hd ho).elim

theorem bound3914 : BoxMajorant Geometry.b3914 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3914.Widths)
  · have he : Geometry.b3914.half 0 false=Geometry.b4279 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4279
  · have he : Geometry.b3914.half 0 true=Geometry.b4280 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4280

theorem bound3913 : BoxMajorant Geometry.b3913 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3913 2 (by decide +kernel) x hx hd ho).elim

theorem bound3578 : BoxMajorant Geometry.b3578 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3578.Widths)
  · have he : Geometry.b3578.half 2 false=Geometry.b3919 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3919
  · have he : Geometry.b3578.half 2 true=Geometry.b3920 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3920

theorem bound3577 : BoxMajorant Geometry.b3577 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3577.Widths)
  · have he : Geometry.b3577.half 2 false=Geometry.b3917 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3917
  · have he : Geometry.b3577.half 2 true=Geometry.b3918 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3918

theorem bound3576 : BoxMajorant Geometry.b3576 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3576.Widths)
  · have he : Geometry.b3576.half 2 false=Geometry.b3915 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3915
  · have he : Geometry.b3576.half 2 true=Geometry.b3916 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3916

theorem bound3575 : BoxMajorant Geometry.b3575 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3575.Widths)
  · have he : Geometry.b3575.half 2 false=Geometry.b3913 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3913
  · have he : Geometry.b3575.half 2 true=Geometry.b3914 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3914

theorem bound3302 : BoxMajorant Geometry.b3302 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3302.Widths)
  · have he : Geometry.b3302.half 1 false=Geometry.b3577 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3577
  · have he : Geometry.b3302.half 1 true=Geometry.b3578 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3578

theorem bound3301 : BoxMajorant Geometry.b3301 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3301.Widths)
  · have he : Geometry.b3301.half 1 false=Geometry.b3575 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3575
  · have he : Geometry.b3301.half 1 true=Geometry.b3576 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3576

theorem bound2966 : BoxMajorant Geometry.b2966 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2966.Widths)
  · have he : Geometry.b2966.half 0 false=Geometry.b3301 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3301
  · have he : Geometry.b2966.half 0 true=Geometry.b3302 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3302

end N7.Kernel.Cover
