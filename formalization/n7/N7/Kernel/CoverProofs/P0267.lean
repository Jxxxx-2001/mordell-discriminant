import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0401
import N7.Kernel.PositiveGroups.G0418
import N7.Kernel.PositiveGroups.G0419
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5192 : BoxMajorant Geometry.b5192 := by
  exact PositiveLeaves.L1746.bound

theorem bound5191 : BoxMajorant Geometry.b5191 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5191 2 (by decide +kernel) x hx hd ho).elim

theorem bound4926 : BoxMajorant Geometry.b4926 := by
  exact PositiveLeaves.L1738.bound

theorem bound4925 : BoxMajorant Geometry.b4925 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4925 2 (by decide +kernel) x hx hd ho).elim

theorem bound4924 : BoxMajorant Geometry.b4924 := by
  exact PositiveLeaves.L1740.bound

theorem bound4923 : BoxMajorant Geometry.b4923 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4923 2 (by decide +kernel) x hx hd ho).elim

theorem bound4922 : BoxMajorant Geometry.b4922 := by
  exact PositiveLeaves.L1744.bound

theorem bound4921 : BoxMajorant Geometry.b4921 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4921 2 (by decide +kernel) x hx hd ho).elim

theorem bound4920 : BoxMajorant Geometry.b4920 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4920.Widths)
  · have he : Geometry.b4920.half 0 false=Geometry.b5191 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5191
  · have he : Geometry.b4920.half 0 true=Geometry.b5192 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5192

theorem bound4919 : BoxMajorant Geometry.b4919 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4919 2 (by decide +kernel) x hx hd ho).elim

theorem bound4586 : BoxMajorant Geometry.b4586 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4586.Widths)
  · have he : Geometry.b4586.half 2 false=Geometry.b4925 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4925
  · have he : Geometry.b4586.half 2 true=Geometry.b4926 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4926

theorem bound4585 : BoxMajorant Geometry.b4585 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4585.Widths)
  · have he : Geometry.b4585.half 2 false=Geometry.b4923 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4923
  · have he : Geometry.b4585.half 2 true=Geometry.b4924 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4924

theorem bound4584 : BoxMajorant Geometry.b4584 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4584.Widths)
  · have he : Geometry.b4584.half 2 false=Geometry.b4921 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4921
  · have he : Geometry.b4584.half 2 true=Geometry.b4922 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4922

theorem bound4583 : BoxMajorant Geometry.b4583 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4583.Widths)
  · have he : Geometry.b4583.half 2 false=Geometry.b4919 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4919
  · have he : Geometry.b4583.half 2 true=Geometry.b4920 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4920

theorem bound4318 : BoxMajorant Geometry.b4318 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4318.Widths)
  · have he : Geometry.b4318.half 1 false=Geometry.b4585 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4585
  · have he : Geometry.b4318.half 1 true=Geometry.b4586 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4586

theorem bound4317 : BoxMajorant Geometry.b4317 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4317 2 (by decide +kernel) x hx hd ho).elim

theorem bound4316 : BoxMajorant Geometry.b4316 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4316.Widths)
  · have he : Geometry.b4316.half 1 false=Geometry.b4583 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4583
  · have he : Geometry.b4316.half 1 true=Geometry.b4584 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4584

theorem bound4315 : BoxMajorant Geometry.b4315 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4315 2 (by decide +kernel) x hx hd ho).elim

theorem bound3964 : BoxMajorant Geometry.b3964 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3964.Widths)
  · have he : Geometry.b3964.half 0 false=Geometry.b4317 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4317
  · have he : Geometry.b3964.half 0 true=Geometry.b4318 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4318

theorem bound3963 : BoxMajorant Geometry.b3963 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3963 2 (by decide +kernel) x hx hd ho).elim

theorem bound3962 : BoxMajorant Geometry.b3962 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3962.Widths)
  · have he : Geometry.b3962.half 0 false=Geometry.b4315 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4315
  · have he : Geometry.b3962.half 0 true=Geometry.b4316 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4316

theorem bound3961 : BoxMajorant Geometry.b3961 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3961 2 (by decide +kernel) x hx hd ho).elim

theorem bound3604 : BoxMajorant Geometry.b3604 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3604.Widths)
  · have he : Geometry.b3604.half 2 false=Geometry.b3963 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3963
  · have he : Geometry.b3604.half 2 true=Geometry.b3964 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3964

theorem bound3603 : BoxMajorant Geometry.b3603 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3603.Widths)
  · have he : Geometry.b3603.half 2 false=Geometry.b3961 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3961
  · have he : Geometry.b3603.half 2 true=Geometry.b3962 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3962

theorem bound3334 : BoxMajorant Geometry.b3334 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3334.Widths)
  · have he : Geometry.b3334.half 1 false=Geometry.b3603 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3603
  · have he : Geometry.b3334.half 1 true=Geometry.b3604 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3604

theorem bound3333 : BoxMajorant Geometry.b3333 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3333 2 (by decide +kernel) x hx hd ho).elim

theorem bound2997 : BoxMajorant Geometry.b2997 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2997.Widths)
  · have he : Geometry.b2997.half 0 false=Geometry.b3333 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3333
  · have he : Geometry.b2997.half 0 true=Geometry.b3334 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3334

end N7.Kernel.Cover
