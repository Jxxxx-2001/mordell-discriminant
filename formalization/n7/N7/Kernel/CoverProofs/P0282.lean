import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0397
import N7.Kernel.PositiveGroups.G0414
import N7.Kernel.PositiveGroups.G0415
import N7.Kernel.PositiveGroups.G0416
import N7.Kernel.PositiveGroups.G0434
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5480 : BoxMajorant Geometry.b5480 := by
  exact PositiveLeaves.L1522.bound

theorem bound5479 : BoxMajorant Geometry.b5479 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5479 2 (by decide +kernel) x hx hd ho).elim

theorem bound5348 : BoxMajorant Geometry.b5348 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5348.Widths)
  · have he : Geometry.b5348.half 2 false=Geometry.b5479 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5479
  · have he : Geometry.b5348.half 2 true=Geometry.b5480 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5480

theorem bound5347 : BoxMajorant Geometry.b5347 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5347 2 (by decide +kernel) x hx hd ho).elim

theorem bound5226 : BoxMajorant Geometry.b5226 := by
  exact PositiveLeaves.L1521.bound

theorem bound5225 : BoxMajorant Geometry.b5225 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5225.Widths)
  · have he : Geometry.b5225.half 1 false=Geometry.b5347 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5347
  · have he : Geometry.b5225.half 1 true=Geometry.b5348 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5348

theorem bound5224 : BoxMajorant Geometry.b5224 := by
  exact PositiveLeaves.L1526.bound

theorem bound5223 : BoxMajorant Geometry.b5223 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5223 2 (by decide +kernel) x hx hd ho).elim

theorem bound5222 : BoxMajorant Geometry.b5222 := by
  exact PositiveLeaves.L1528.bound

theorem bound5221 : BoxMajorant Geometry.b5221 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5221 2 (by decide +kernel) x hx hd ho).elim

theorem bound5220 : BoxMajorant Geometry.b5220 := by
  exact PositiveLeaves.L1531.bound

theorem bound5219 : BoxMajorant Geometry.b5219 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5219 2 (by decide +kernel) x hx hd ho).elim

theorem bound4998 : BoxMajorant Geometry.b4998 := by
  exact PositiveLeaves.L1520.bound

theorem bound4997 : BoxMajorant Geometry.b4997 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4997.Widths)
  · have he : Geometry.b4997.half 0 false=Geometry.b5225 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5225
  · have he : Geometry.b4997.half 0 true=Geometry.b5226 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5226

theorem bound4996 : BoxMajorant Geometry.b4996 := by
  exact PositiveLeaves.L1525.bound

theorem bound4995 : BoxMajorant Geometry.b4995 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4995.Widths)
  · have he : Geometry.b4995.half 0 false=Geometry.b5223 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5223
  · have he : Geometry.b4995.half 0 true=Geometry.b5224 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5224

theorem bound4994 : BoxMajorant Geometry.b4994 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4994.Widths)
  · have he : Geometry.b4994.half 0 false=Geometry.b5221 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5221
  · have he : Geometry.b4994.half 0 true=Geometry.b5222 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5222

theorem bound4993 : BoxMajorant Geometry.b4993 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4993 2 (by decide +kernel) x hx hd ho).elim

theorem bound4992 : BoxMajorant Geometry.b4992 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4992.Widths)
  · have he : Geometry.b4992.half 0 false=Geometry.b5219 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5219
  · have he : Geometry.b4992.half 0 true=Geometry.b5220 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5220

theorem bound4991 : BoxMajorant Geometry.b4991 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4991 2 (by decide +kernel) x hx hd ho).elim

theorem bound4640 : BoxMajorant Geometry.b4640 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4640.Widths)
  · have he : Geometry.b4640.half 2 false=Geometry.b4997 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4997
  · have he : Geometry.b4640.half 2 true=Geometry.b4998 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4998

theorem bound4639 : BoxMajorant Geometry.b4639 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4639.Widths)
  · have he : Geometry.b4639.half 2 false=Geometry.b4995 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4995
  · have he : Geometry.b4639.half 2 true=Geometry.b4996 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4996

theorem bound4638 : BoxMajorant Geometry.b4638 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4638.Widths)
  · have he : Geometry.b4638.half 2 false=Geometry.b4993 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4993
  · have he : Geometry.b4638.half 2 true=Geometry.b4994 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4994

theorem bound4637 : BoxMajorant Geometry.b4637 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4637.Widths)
  · have he : Geometry.b4637.half 2 false=Geometry.b4991 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4991
  · have he : Geometry.b4637.half 2 true=Geometry.b4992 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4992

theorem bound4378 : BoxMajorant Geometry.b4378 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4378.Widths)
  · have he : Geometry.b4378.half 1 false=Geometry.b4639 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4639
  · have he : Geometry.b4378.half 1 true=Geometry.b4640 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4640

theorem bound4377 : BoxMajorant Geometry.b4377 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4377.Widths)
  · have he : Geometry.b4377.half 1 false=Geometry.b4637 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4637
  · have he : Geometry.b4377.half 1 true=Geometry.b4638 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4638

theorem bound4032 : BoxMajorant Geometry.b4032 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4032.Widths)
  · have he : Geometry.b4032.half 0 false=Geometry.b4377 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4377
  · have he : Geometry.b4032.half 0 true=Geometry.b4378 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4378

end N7.Kernel.Cover
