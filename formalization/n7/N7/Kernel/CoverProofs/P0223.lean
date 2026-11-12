import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverProofs.P0362
import N7.Kernel.CoverProofs.P0363
import N7.Kernel.CoverProofs.P0364
import N7.Kernel.PositiveGroups.G0316
import N7.Kernel.PositiveGroups.G0347
import N7.Kernel.PositiveGroups.G0378
import N7.Kernel.PositiveGroups.G0379
import N7.Kernel.PositiveGroups.G0403
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4550 : BoxMajorant Geometry.b4550 := by
  exact PositiveLeaves.L1963.bound

theorem bound4264 : BoxMajorant Geometry.b4264 := by
  exact PositiveLeaves.L1962.bound

theorem bound4263 : BoxMajorant Geometry.b4263 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4263.Widths)
  · have he : Geometry.b4263.half 1 false=Geometry.b4549 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4549
  · have he : Geometry.b4263.half 1 true=Geometry.b4550 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4550

theorem bound4262 : BoxMajorant Geometry.b4262 := by
  exact PositiveLeaves.L1968.bound

theorem bound4261 : BoxMajorant Geometry.b4261 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4261 2 (by decide +kernel) x hx hd ho).elim

theorem bound4260 : BoxMajorant Geometry.b4260 := by
  exact PositiveLeaves.L1971.bound

theorem bound4259 : BoxMajorant Geometry.b4259 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4259 2 (by decide +kernel) x hx hd ho).elim

theorem bound4258 : BoxMajorant Geometry.b4258 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4258.Widths)
  · have he : Geometry.b4258.half 1 false=Geometry.b4547 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4547
  · have he : Geometry.b4258.half 1 true=Geometry.b4548 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4548

theorem bound4257 : BoxMajorant Geometry.b4257 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4257 2 (by decide +kernel) x hx hd ho).elim

theorem bound3896 : BoxMajorant Geometry.b3896 := by
  exact PositiveLeaves.L1961.bound

theorem bound3895 : BoxMajorant Geometry.b3895 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3895.Widths)
  · have he : Geometry.b3895.half 0 false=Geometry.b4263 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4263
  · have he : Geometry.b3895.half 0 true=Geometry.b4264 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4264

theorem bound3894 : BoxMajorant Geometry.b3894 := by
  exact PositiveLeaves.L1966.bound

theorem bound3893 : BoxMajorant Geometry.b3893 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3893 2 (by decide +kernel) x hx hd ho).elim

theorem bound3892 : BoxMajorant Geometry.b3892 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3892.Widths)
  · have he : Geometry.b3892.half 0 false=Geometry.b4261 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4261
  · have he : Geometry.b3892.half 0 true=Geometry.b4262 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4262

theorem bound3891 : BoxMajorant Geometry.b3891 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3891 2 (by decide +kernel) x hx hd ho).elim

theorem bound3890 : BoxMajorant Geometry.b3890 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3890.Widths)
  · have he : Geometry.b3890.half 0 false=Geometry.b4259 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4259
  · have he : Geometry.b3890.half 0 true=Geometry.b4260 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4260

theorem bound3889 : BoxMajorant Geometry.b3889 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3889 2 (by decide +kernel) x hx hd ho).elim

theorem bound3888 : BoxMajorant Geometry.b3888 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3888.Widths)
  · have he : Geometry.b3888.half 0 false=Geometry.b4257 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4257
  · have he : Geometry.b3888.half 0 true=Geometry.b4258 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4258

theorem bound3887 : BoxMajorant Geometry.b3887 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3887 2 (by decide +kernel) x hx hd ho).elim

theorem bound3564 : BoxMajorant Geometry.b3564 := by
  exact PositiveLeaves.L1960.bound

theorem bound3563 : BoxMajorant Geometry.b3563 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3563.Widths)
  · have he : Geometry.b3563.half 2 false=Geometry.b3895 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3895
  · have he : Geometry.b3563.half 2 true=Geometry.b3896 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3896

theorem bound3562 : BoxMajorant Geometry.b3562 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3562.Widths)
  · have he : Geometry.b3562.half 2 false=Geometry.b3893 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3893
  · have he : Geometry.b3562.half 2 true=Geometry.b3894 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3894

theorem bound3561 : BoxMajorant Geometry.b3561 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3561.Widths)
  · have he : Geometry.b3561.half 2 false=Geometry.b3891 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3891
  · have he : Geometry.b3561.half 2 true=Geometry.b3892 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3892

theorem bound3560 : BoxMajorant Geometry.b3560 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3560.Widths)
  · have he : Geometry.b3560.half 2 false=Geometry.b3889 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3889
  · have he : Geometry.b3560.half 2 true=Geometry.b3890 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3890

theorem bound3559 : BoxMajorant Geometry.b3559 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3559.Widths)
  · have he : Geometry.b3559.half 2 false=Geometry.b3887 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3887
  · have he : Geometry.b3559.half 2 true=Geometry.b3888 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3888

theorem bound3286 : BoxMajorant Geometry.b3286 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3286.Widths)
  · have he : Geometry.b3286.half 1 false=Geometry.b3563 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3563
  · have he : Geometry.b3286.half 1 true=Geometry.b3564 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3564

theorem bound3285 : BoxMajorant Geometry.b3285 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3285.Widths)
  · have he : Geometry.b3285.half 1 false=Geometry.b3561 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3561
  · have he : Geometry.b3285.half 1 true=Geometry.b3562 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3562

theorem bound3284 : BoxMajorant Geometry.b3284 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3284.Widths)
  · have he : Geometry.b3284.half 1 false=Geometry.b3559 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3559
  · have he : Geometry.b3284.half 1 true=Geometry.b3560 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3560

theorem bound3283 : BoxMajorant Geometry.b3283 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3283 2 (by decide +kernel) x hx hd ho).elim

theorem bound2952 : BoxMajorant Geometry.b2952 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2952.Widths)
  · have he : Geometry.b2952.half 0 false=Geometry.b3285 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3285
  · have he : Geometry.b2952.half 0 true=Geometry.b3286 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3286

theorem bound2951 : BoxMajorant Geometry.b2951 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2951.Widths)
  · have he : Geometry.b2951.half 0 false=Geometry.b3283 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3283
  · have he : Geometry.b2951.half 0 true=Geometry.b3284 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3284

theorem bound2589 : BoxMajorant Geometry.b2589 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2589.Widths)
  · have he : Geometry.b2589.half 2 false=Geometry.b2951 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2951
  · have he : Geometry.b2589.half 2 true=Geometry.b2952 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2952

end N7.Kernel.Cover
