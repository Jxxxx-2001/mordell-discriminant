import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.PositiveGroups.G0376
import N7.Kernel.PositiveGroups.G0377
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4240 : BoxMajorant Geometry.b4240 := by
  exact PositiveLeaves.L2030.bound

theorem bound4239 : BoxMajorant Geometry.b4239 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4239 2 (by decide +kernel) x hx hd ho).elim

theorem bound4238 : BoxMajorant Geometry.b4238 := by
  exact PositiveLeaves.L2033.bound

theorem bound4237 : BoxMajorant Geometry.b4237 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4237 2 (by decide +kernel) x hx hd ho).elim

theorem bound3868 : BoxMajorant Geometry.b3868 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3868.Widths)
  · have he : Geometry.b3868.half 0 false=Geometry.b4239 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4239
  · have he : Geometry.b3868.half 0 true=Geometry.b4240 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4240

theorem bound3867 : BoxMajorant Geometry.b3867 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3867 2 (by decide +kernel) x hx hd ho).elim

theorem bound3866 : BoxMajorant Geometry.b3866 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3866.Widths)
  · have he : Geometry.b3866.half 0 false=Geometry.b4237 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4237
  · have he : Geometry.b3866.half 0 true=Geometry.b4238 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4238

theorem bound3865 : BoxMajorant Geometry.b3865 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3865 2 (by decide +kernel) x hx hd ho).elim

theorem bound3548 : BoxMajorant Geometry.b3548 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3548.Widths)
  · have he : Geometry.b3548.half 2 false=Geometry.b3867 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3867
  · have he : Geometry.b3548.half 2 true=Geometry.b3868 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3868

theorem bound3547 : BoxMajorant Geometry.b3547 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3547.Widths)
  · have he : Geometry.b3547.half 2 false=Geometry.b3865 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3865
  · have he : Geometry.b3547.half 2 true=Geometry.b3866 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3866

theorem bound3272 : BoxMajorant Geometry.b3272 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3272.Widths)
  · have he : Geometry.b3272.half 1 false=Geometry.b3547 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3547
  · have he : Geometry.b3272.half 1 true=Geometry.b3548 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3548

theorem bound3271 : BoxMajorant Geometry.b3271 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3271 2 (by decide +kernel) x hx hd ho).elim

theorem bound2943 : BoxMajorant Geometry.b2943 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2943.Widths)
  · have he : Geometry.b2943.half 0 false=Geometry.b3271 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3271
  · have he : Geometry.b2943.half 0 true=Geometry.b3272 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3272

end N7.Kernel.Cover
