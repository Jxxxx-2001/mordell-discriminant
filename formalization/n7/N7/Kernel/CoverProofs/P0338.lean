import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0385
import N7.Kernel.PositiveGroups.G0409
import N7.Kernel.PositiveGroups.G0426
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5420 : BoxMajorant Geometry.b5420 := by
  exact PositiveLeaves.L2859.bound

theorem bound5419 : BoxMajorant Geometry.b5419 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5419 2 (by decide +kernel) x hx hd ho).elim

theorem bound5294 : BoxMajorant Geometry.b5294 := by
  exact PositiveLeaves.L2858.bound

theorem bound5293 : BoxMajorant Geometry.b5293 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5293.Widths)
  · have he : Geometry.b5293.half 2 false=Geometry.b5419 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5419
  · have he : Geometry.b5293.half 2 true=Geometry.b5420 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5420

theorem bound5116 : BoxMajorant Geometry.b5116 := by
  exact PositiveLeaves.L2857.bound

theorem bound5115 : BoxMajorant Geometry.b5115 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5115.Widths)
  · have he : Geometry.b5115.half 1 false=Geometry.b5293 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5293
  · have he : Geometry.b5115.half 1 true=Geometry.b5294 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5294

theorem bound4734 : BoxMajorant Geometry.b4734 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4734.Widths)
  · have he : Geometry.b4734.half 0 false=Geometry.b5115 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5115
  · have he : Geometry.b4734.half 0 true=Geometry.b5116 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5116

end N7.Kernel.Cover
