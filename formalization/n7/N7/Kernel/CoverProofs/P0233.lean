import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.PositiveGroups.G0292
import N7.Kernel.PositiveGroups.G0345
import N7.Kernel.PositiveGroups.G0377
import N7.Kernel.PositiveGroups.G0378
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4250 : BoxMajorant Geometry.b4250 := by
  exact PositiveLeaves.L2008.bound

theorem bound4249 : BoxMajorant Geometry.b4249 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4249 2 (by decide +kernel) x hx hd ho).elim

theorem bound4248 : BoxMajorant Geometry.b4248 := by
  exact PositiveLeaves.L2011.bound

theorem bound4247 : BoxMajorant Geometry.b4247 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4247 2 (by decide +kernel) x hx hd ho).elim

theorem bound3880 : BoxMajorant Geometry.b3880 := by
  exact PositiveLeaves.L2007.bound

theorem bound3879 : BoxMajorant Geometry.b3879 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3879.Widths)
  · have he : Geometry.b3879.half 0 false=Geometry.b4249 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4249
  · have he : Geometry.b3879.half 0 true=Geometry.b4250 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4250

theorem bound3878 : BoxMajorant Geometry.b3878 := by
  exact PositiveLeaves.L2010.bound

theorem bound3877 : BoxMajorant Geometry.b3877 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3877.Widths)
  · have he : Geometry.b3877.half 0 false=Geometry.b4247 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4247
  · have he : Geometry.b3877.half 0 true=Geometry.b4248 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4248

theorem bound3554 : BoxMajorant Geometry.b3554 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3554.Widths)
  · have he : Geometry.b3554.half 2 false=Geometry.b3879 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3879
  · have he : Geometry.b3554.half 2 true=Geometry.b3880 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3880

theorem bound3553 : BoxMajorant Geometry.b3553 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3553.Widths)
  · have he : Geometry.b3553.half 2 false=Geometry.b3877 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3877
  · have he : Geometry.b3553.half 2 true=Geometry.b3878 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3878

theorem bound3278 : BoxMajorant Geometry.b3278 := by
  exact PositiveLeaves.L2006.bound

theorem bound3277 : BoxMajorant Geometry.b3277 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3277.Widths)
  · have he : Geometry.b3277.half 1 false=Geometry.b3553 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3553
  · have he : Geometry.b3277.half 1 true=Geometry.b3554 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3554

theorem bound2946 : BoxMajorant Geometry.b2946 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2946.Widths)
  · have he : Geometry.b2946.half 0 false=Geometry.b3277 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3277
  · have he : Geometry.b2946.half 0 true=Geometry.b3278 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3278

end N7.Kernel.Cover
