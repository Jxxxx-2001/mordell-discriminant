import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.PositiveGroups.G0318
import N7.Kernel.PositiveGroups.G0350
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4814 : BoxMajorant Geometry.b4814 := by
  exact PositiveLeaves.L2132.bound

theorem bound4813 : BoxMajorant Geometry.b4813 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4813 2 (by decide +kernel) x hx hd ho).elim

theorem bound4812 : BoxMajorant Geometry.b4812 := by
  exact PositiveLeaves.L2134.bound

theorem bound4811 : BoxMajorant Geometry.b4811 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4811 2 (by decide +kernel) x hx hd ho).elim

theorem bound4518 : BoxMajorant Geometry.b4518 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4518.Widths)
  · have he : Geometry.b4518.half 2 false=Geometry.b4813 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4813
  · have he : Geometry.b4518.half 2 true=Geometry.b4814 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4814

theorem bound4517 : BoxMajorant Geometry.b4517 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4517.Widths)
  · have he : Geometry.b4517.half 2 false=Geometry.b4811 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4811
  · have he : Geometry.b4517.half 2 true=Geometry.b4812 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4812

theorem bound4214 : BoxMajorant Geometry.b4214 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4214.Widths)
  · have he : Geometry.b4214.half 1 false=Geometry.b4517 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4517
  · have he : Geometry.b4214.half 1 true=Geometry.b4518 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4518

theorem bound4213 : BoxMajorant Geometry.b4213 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4213 2 (by decide +kernel) x hx hd ho).elim

theorem bound3834 : BoxMajorant Geometry.b3834 := by
  exact PositiveLeaves.L2131.bound

theorem bound3833 : BoxMajorant Geometry.b3833 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3833.Widths)
  · have he : Geometry.b3833.half 0 false=Geometry.b4213 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4213
  · have he : Geometry.b3833.half 0 true=Geometry.b4214 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4214

theorem bound3832 : BoxMajorant Geometry.b3832 := by
  exact PositiveLeaves.L2137.bound

theorem bound3831 : BoxMajorant Geometry.b3831 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3831 2 (by decide +kernel) x hx hd ho).elim

theorem bound3528 : BoxMajorant Geometry.b3528 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3528.Widths)
  · have he : Geometry.b3528.half 2 false=Geometry.b3833 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3833
  · have he : Geometry.b3528.half 2 true=Geometry.b3834 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3834

theorem bound3527 : BoxMajorant Geometry.b3527 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3527.Widths)
  · have he : Geometry.b3527.half 2 false=Geometry.b3831 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3831
  · have he : Geometry.b3527.half 2 true=Geometry.b3832 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3832

theorem bound3254 : BoxMajorant Geometry.b3254 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3254.Widths)
  · have he : Geometry.b3254.half 1 false=Geometry.b3527 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3527
  · have he : Geometry.b3254.half 1 true=Geometry.b3528 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3528

theorem bound3253 : BoxMajorant Geometry.b3253 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3253 2 (by decide +kernel) x hx hd ho).elim

theorem bound2930 : BoxMajorant Geometry.b2930 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2930.Widths)
  · have he : Geometry.b2930.half 0 false=Geometry.b3253 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3253
  · have he : Geometry.b2930.half 0 true=Geometry.b3254 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3254

end N7.Kernel.Cover
