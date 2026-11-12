import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0397
import N7.Kernel.PositiveGroups.G0415
import N7.Kernel.PositiveGroups.G0416
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5218 : BoxMajorant Geometry.b5218 := by
  exact PositiveLeaves.L1536.bound

theorem bound5217 : BoxMajorant Geometry.b5217 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5217 2 (by decide +kernel) x hx hd ho).elim

theorem bound5216 : BoxMajorant Geometry.b5216 := by
  exact PositiveLeaves.L1539.bound

theorem bound5215 : BoxMajorant Geometry.b5215 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5215 2 (by decide +kernel) x hx hd ho).elim

theorem bound5214 : BoxMajorant Geometry.b5214 := by
  exact PositiveLeaves.L1541.bound

theorem bound5213 : BoxMajorant Geometry.b5213 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5213 2 (by decide +kernel) x hx hd ho).elim

theorem bound4990 : BoxMajorant Geometry.b4990 := by
  exact PositiveLeaves.L1535.bound

theorem bound4989 : BoxMajorant Geometry.b4989 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4989.Widths)
  · have he : Geometry.b4989.half 0 false=Geometry.b5217 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5217
  · have he : Geometry.b4989.half 0 true=Geometry.b5218 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5218

theorem bound4988 : BoxMajorant Geometry.b4988 := by
  exact PositiveLeaves.L1538.bound

theorem bound4987 : BoxMajorant Geometry.b4987 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4987.Widths)
  · have he : Geometry.b4987.half 0 false=Geometry.b5215 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5215
  · have he : Geometry.b4987.half 0 true=Geometry.b5216 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5216

theorem bound4986 : BoxMajorant Geometry.b4986 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4986.Widths)
  · have he : Geometry.b4986.half 0 false=Geometry.b5213 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5213
  · have he : Geometry.b4986.half 0 true=Geometry.b5214 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5214

theorem bound4985 : BoxMajorant Geometry.b4985 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4985 2 (by decide +kernel) x hx hd ho).elim

theorem bound4636 : BoxMajorant Geometry.b4636 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4636.Widths)
  · have he : Geometry.b4636.half 2 false=Geometry.b4989 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4989
  · have he : Geometry.b4636.half 2 true=Geometry.b4990 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4990

theorem bound4635 : BoxMajorant Geometry.b4635 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4635.Widths)
  · have he : Geometry.b4635.half 2 false=Geometry.b4987 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4987
  · have he : Geometry.b4635.half 2 true=Geometry.b4988 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4988

theorem bound4634 : BoxMajorant Geometry.b4634 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4634.Widths)
  · have he : Geometry.b4634.half 2 false=Geometry.b4985 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4985
  · have he : Geometry.b4634.half 2 true=Geometry.b4986 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4986

theorem bound4633 : BoxMajorant Geometry.b4633 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4633 2 (by decide +kernel) x hx hd ho).elim

theorem bound4376 : BoxMajorant Geometry.b4376 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4376.Widths)
  · have he : Geometry.b4376.half 1 false=Geometry.b4635 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4635
  · have he : Geometry.b4376.half 1 true=Geometry.b4636 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4636

theorem bound4375 : BoxMajorant Geometry.b4375 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4375.Widths)
  · have he : Geometry.b4375.half 1 false=Geometry.b4633 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4633
  · have he : Geometry.b4375.half 1 true=Geometry.b4634 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4634

theorem bound4030 : BoxMajorant Geometry.b4030 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4030.Widths)
  · have he : Geometry.b4030.half 0 false=Geometry.b4375 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4375
  · have he : Geometry.b4030.half 0 true=Geometry.b4376 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4376

end N7.Kernel.Cover
