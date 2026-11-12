import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0408
import N7.Kernel.PositiveGroups.G0425
import N7.Kernel.PositiveGroups.G0439
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5456 : BoxMajorant Geometry.b5456 := by
  exact PositiveLeaves.L2773.bound

theorem bound5455 : BoxMajorant Geometry.b5455 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5455 2 (by decide +kernel) x hx hd ho).elim

theorem bound5324 : BoxMajorant Geometry.b5324 := by
  exact PositiveLeaves.L2772.bound

theorem bound5323 : BoxMajorant Geometry.b5323 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5323.Widths)
  · have he : Geometry.b5323.half 2 false=Geometry.b5455 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5455
  · have he : Geometry.b5323.half 2 true=Geometry.b5456 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5456

theorem bound5140 : BoxMajorant Geometry.b5140 := by
  exact PositiveLeaves.L2771.bound

theorem bound5139 : BoxMajorant Geometry.b5139 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5139.Widths)
  · have he : Geometry.b5139.half 1 false=Geometry.b5323 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5323
  · have he : Geometry.b5139.half 1 true=Geometry.b5324 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5324

theorem bound4764 : BoxMajorant Geometry.b4764 := by
  exact PositiveLeaves.L2770.bound

theorem bound4763 : BoxMajorant Geometry.b4763 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4763.Widths)
  · have he : Geometry.b4763.half 0 false=Geometry.b5139 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5139
  · have he : Geometry.b4763.half 0 true=Geometry.b5140 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5140

theorem bound4475 : BoxMajorant Geometry.b4475 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4475.Widths)
  · have he : Geometry.b4475.half 2 false=Geometry.b4763 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4763
  · have he : Geometry.b4475.half 2 true=Geometry.b4764 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4764

end N7.Kernel.Cover
