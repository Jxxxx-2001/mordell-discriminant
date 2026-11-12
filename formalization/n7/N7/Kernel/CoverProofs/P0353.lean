import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0439
import N7.Kernel.PositiveGroups.G0453
import N7.Kernel.PositiveGroups.G0462
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5454 : BoxMajorant Geometry.b5454 := by
  exact PositiveLeaves.L2794.bound

theorem bound5453 : BoxMajorant Geometry.b5453 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5453 2 (by decide +kernel) x hx hd ho).elim

theorem bound5322 : BoxMajorant Geometry.b5322 := by
  exact PositiveLeaves.L2793.bound

theorem bound5321 : BoxMajorant Geometry.b5321 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5321.Widths)
  · have he : Geometry.b5321.half 2 false=Geometry.b5453 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5453
  · have he : Geometry.b5321.half 2 true=Geometry.b5454 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5454

theorem bound5134 : BoxMajorant Geometry.b5134 := by
  exact PositiveLeaves.L2792.bound

theorem bound5133 : BoxMajorant Geometry.b5133 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5133.Widths)
  · have he : Geometry.b5133.half 1 false=Geometry.b5321 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5321
  · have he : Geometry.b5133.half 1 true=Geometry.b5322 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5322

theorem bound4753 : BoxMajorant Geometry.b4753 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4753.Widths)
  · have he : Geometry.b4753.half 0 false=Geometry.b5133 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5133
  · have he : Geometry.b4753.half 0 true=Geometry.b5134 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5134

end N7.Kernel.Cover
