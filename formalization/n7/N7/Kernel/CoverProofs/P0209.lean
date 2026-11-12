import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.PositiveGroups.G0184
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3806 : BoxMajorant Geometry.b3806 := by
  exact PositiveLeaves.L2491.bound

theorem bound3805 : BoxMajorant Geometry.b3805 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3805 2 (by decide +kernel) x hx hd ho).elim

theorem bound3508 : BoxMajorant Geometry.b3508 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3508.Widths)
  · have he : Geometry.b3508.half 2 false=Geometry.b3805 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3805
  · have he : Geometry.b3508.half 2 true=Geometry.b3806 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3806

theorem bound3507 : BoxMajorant Geometry.b3507 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3507 2 (by decide +kernel) x hx hd ho).elim

theorem bound3224 : BoxMajorant Geometry.b3224 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3224.Widths)
  · have he : Geometry.b3224.half 1 false=Geometry.b3507 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3507
  · have he : Geometry.b3224.half 1 true=Geometry.b3508 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3508

end N7.Kernel.Cover
