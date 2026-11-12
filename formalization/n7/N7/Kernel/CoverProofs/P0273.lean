import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0310
import N7.Kernel.PositiveGroups.G0334
import N7.Kernel.PositiveGroups.G0414
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5230 : BoxMajorant Geometry.b5230 := by
  exact PositiveLeaves.L1514.bound

theorem bound5229 : BoxMajorant Geometry.b5229 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5229 2 (by decide +kernel) x hx hd ho).elim

theorem bound5228 : BoxMajorant Geometry.b5228 := by
  exact PositiveLeaves.L1517.bound

theorem bound5227 : BoxMajorant Geometry.b5227 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5227 2 (by decide +kernel) x hx hd ho).elim

theorem bound5002 : BoxMajorant Geometry.b5002 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5002.Widths)
  · have he : Geometry.b5002.half 0 false=Geometry.b5229 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5229
  · have he : Geometry.b5002.half 0 true=Geometry.b5230 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5230

theorem bound5001 : BoxMajorant Geometry.b5001 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5001 2 (by decide +kernel) x hx hd ho).elim

theorem bound5000 : BoxMajorant Geometry.b5000 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5000.Widths)
  · have he : Geometry.b5000.half 0 false=Geometry.b5227 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5227
  · have he : Geometry.b5000.half 0 true=Geometry.b5228 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5228

theorem bound4999 : BoxMajorant Geometry.b4999 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4999 2 (by decide +kernel) x hx hd ho).elim

theorem bound4642 : BoxMajorant Geometry.b4642 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4642.Widths)
  · have he : Geometry.b4642.half 2 false=Geometry.b5001 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5001
  · have he : Geometry.b4642.half 2 true=Geometry.b5002 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5002

theorem bound4641 : BoxMajorant Geometry.b4641 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4641.Widths)
  · have he : Geometry.b4641.half 2 false=Geometry.b4999 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4999
  · have he : Geometry.b4641.half 2 true=Geometry.b5000 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5000

theorem bound4380 : BoxMajorant Geometry.b4380 := by
  exact PositiveLeaves.L1513.bound

theorem bound4379 : BoxMajorant Geometry.b4379 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4379.Widths)
  · have he : Geometry.b4379.half 1 false=Geometry.b4641 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4641
  · have he : Geometry.b4379.half 1 true=Geometry.b4642 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4642

theorem bound4034 : BoxMajorant Geometry.b4034 := by
  exact PositiveLeaves.L1512.bound

theorem bound4033 : BoxMajorant Geometry.b4033 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4033.Widths)
  · have he : Geometry.b4033.half 0 false=Geometry.b4379 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4379
  · have he : Geometry.b4033.half 0 true=Geometry.b4380 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4380

theorem bound3647 : BoxMajorant Geometry.b3647 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3647.Widths)
  · have he : Geometry.b3647.half 2 false=Geometry.b4033 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4033
  · have he : Geometry.b3647.half 2 true=Geometry.b4034 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4034

end N7.Kernel.Cover
