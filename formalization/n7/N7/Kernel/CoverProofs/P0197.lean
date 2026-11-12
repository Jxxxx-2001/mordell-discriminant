import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.PositiveGroups.G0267
import N7.Kernel.PositiveGroups.G0268
import N7.Kernel.PositiveGroups.G0297
import N7.Kernel.PositiveGroups.G0321
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4786 : BoxMajorant Geometry.b4786 := by
  exact PositiveLeaves.L2679.bound

theorem bound4785 : BoxMajorant Geometry.b4785 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4785 2 (by decide +kernel) x hx hd ho).elim

theorem bound4494 : BoxMajorant Geometry.b4494 := by
  exact PositiveLeaves.L2678.bound

theorem bound4493 : BoxMajorant Geometry.b4493 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4493.Widths)
  · have he : Geometry.b4493.half 2 false=Geometry.b4785 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4785
  · have he : Geometry.b4493.half 2 true=Geometry.b4786 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4786

theorem bound4192 : BoxMajorant Geometry.b4192 := by
  exact PositiveLeaves.L2677.bound

theorem bound4191 : BoxMajorant Geometry.b4191 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4191.Widths)
  · have he : Geometry.b4191.half 1 false=Geometry.b4493 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4493
  · have he : Geometry.b4191.half 1 true=Geometry.b4494 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4494

theorem bound3786 : BoxMajorant Geometry.b3786 := by
  exact PositiveLeaves.L2676.bound

theorem bound3785 : BoxMajorant Geometry.b3785 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3785.Widths)
  · have he : Geometry.b3785.half 0 false=Geometry.b4191 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4191
  · have he : Geometry.b3785.half 0 true=Geometry.b4192 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4192

theorem bound3784 : BoxMajorant Geometry.b3784 := by
  exact PositiveLeaves.L2681.bound

theorem bound3783 : BoxMajorant Geometry.b3783 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3783 2 (by decide +kernel) x hx hd ho).elim

theorem bound3782 : BoxMajorant Geometry.b3782 := by
  exact PositiveLeaves.L2683.bound

theorem bound3781 : BoxMajorant Geometry.b3781 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3781 2 (by decide +kernel) x hx hd ho).elim

theorem bound3488 : BoxMajorant Geometry.b3488 := by
  exact PositiveLeaves.L2675.bound

theorem bound3487 : BoxMajorant Geometry.b3487 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3487.Widths)
  · have he : Geometry.b3487.half 2 false=Geometry.b3785 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3785
  · have he : Geometry.b3487.half 2 true=Geometry.b3786 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3786

theorem bound3486 : BoxMajorant Geometry.b3486 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3486.Widths)
  · have he : Geometry.b3486.half 2 false=Geometry.b3783 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3783
  · have he : Geometry.b3486.half 2 true=Geometry.b3784 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3784

theorem bound3485 : BoxMajorant Geometry.b3485 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3485.Widths)
  · have he : Geometry.b3485.half 2 false=Geometry.b3781 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3781
  · have he : Geometry.b3485.half 2 true=Geometry.b3782 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3782

theorem bound3204 : BoxMajorant Geometry.b3204 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3204.Widths)
  · have he : Geometry.b3204.half 1 false=Geometry.b3487 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3487
  · have he : Geometry.b3204.half 1 true=Geometry.b3488 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3488

theorem bound3203 : BoxMajorant Geometry.b3203 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3203.Widths)
  · have he : Geometry.b3203.half 1 false=Geometry.b3485 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3485
  · have he : Geometry.b3203.half 1 true=Geometry.b3486 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3486

theorem bound2825 : BoxMajorant Geometry.b2825 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2825.Widths)
  · have he : Geometry.b2825.half 0 false=Geometry.b3203 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3203
  · have he : Geometry.b2825.half 0 true=Geometry.b3204 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3204

end N7.Kernel.Cover
