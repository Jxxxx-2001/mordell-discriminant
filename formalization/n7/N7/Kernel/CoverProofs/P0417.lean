import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.PositiveGroups.G0483
import N7.Kernel.PositiveGroups.G0490
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5802 : BoxMajorant Geometry.b5802 := by
  exact PositiveLeaves.L303.bound

theorem bound5801 : BoxMajorant Geometry.b5801 := by
  exact PositiveLeaves.L304.bound

theorem bound5738 : BoxMajorant Geometry.b5738 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5738.Widths)
  · have he : Geometry.b5738.half 2 false=Geometry.b5801 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5801
  · have he : Geometry.b5738.half 2 true=Geometry.b5802 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5802

theorem bound5737 : BoxMajorant Geometry.b5737 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5737 0 (by decide +kernel) x hx hd ho).elim

theorem bound5698 : BoxMajorant Geometry.b5698 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5698 0 (by decide +kernel) x hx hd ho).elim

theorem bound5697 : BoxMajorant Geometry.b5697 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5697.Widths)
  · have he : Geometry.b5697.half 1 false=Geometry.b5737 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5737
  · have he : Geometry.b5697.half 1 true=Geometry.b5738 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5738

theorem bound5664 : BoxMajorant Geometry.b5664 := by
  exact PositiveLeaves.L301.bound

theorem bound5663 : BoxMajorant Geometry.b5663 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5663.Widths)
  · have he : Geometry.b5663.half 0 false=Geometry.b5697 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5697
  · have he : Geometry.b5663.half 0 true=Geometry.b5698 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5698

theorem bound5617 : BoxMajorant Geometry.b5617 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5617.Widths)
  · have he : Geometry.b5617.half 2 false=Geometry.b5663 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5663
  · have he : Geometry.b5617.half 2 true=Geometry.b5664 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5664

end N7.Kernel.Cover
