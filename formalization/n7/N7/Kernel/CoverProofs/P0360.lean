import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.LocalBridge
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.Local.C0LargeMajorant
import N7.Kernel.PositiveGroups.G0423
import N7.Kernel.PositiveGroups.G0424
import N7.Kernel.PositiveGroups.G0437
import N7.Kernel.PositiveGroups.G0451
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5744 : BoxMajorant Geometry.b5744 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5744 Local.C0.center Local.C0.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C0.large_near_majorant hn hd.1

theorem bound5743 : BoxMajorant Geometry.b5743 := by
  exact PositiveLeaves.L2190.bound

theorem bound5702 : BoxMajorant Geometry.b5702 := by
  exact PositiveLeaves.L2188.bound

theorem bound5701 : BoxMajorant Geometry.b5701 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5701.Widths)
  · have he : Geometry.b5701.half 2 false=Geometry.b5743 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5743
  · have he : Geometry.b5701.half 2 true=Geometry.b5744 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5744

theorem bound5672 : BoxMajorant Geometry.b5672 := by
  exact PositiveLeaves.L2187.bound

theorem bound5671 : BoxMajorant Geometry.b5671 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5671.Widths)
  · have he : Geometry.b5671.half 1 false=Geometry.b5701 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5701
  · have he : Geometry.b5671.half 1 true=Geometry.b5702 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5702

theorem bound5628 : BoxMajorant Geometry.b5628 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5628.Widths)
  · have he : Geometry.b5628.half 0 false=Geometry.b5671 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5671
  · have he : Geometry.b5628.half 0 true=Geometry.b5672 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5672

theorem bound5627 : BoxMajorant Geometry.b5627 := by
  exact PositiveLeaves.L2191.bound

theorem bound5591 : BoxMajorant Geometry.b5591 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5591.Widths)
  · have he : Geometry.b5591.half 2 false=Geometry.b5627 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5627
  · have he : Geometry.b5591.half 2 true=Geometry.b5628 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5628

end N7.Kernel.Cover
