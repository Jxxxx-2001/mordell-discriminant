import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.PositiveGroups.G0153
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2786 : BoxMajorant Geometry.b2786 := by
  exact PositiveLeaves.L2950.bound

theorem bound2785 : BoxMajorant Geometry.b2785 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2785 2 (by decide +kernel) x hx hd ho).elim

theorem bound2448 : BoxMajorant Geometry.b2448 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2448.Widths)
  · have he : Geometry.b2448.half 2 false=Geometry.b2785 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2785
  · have he : Geometry.b2448.half 2 true=Geometry.b2786 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2786

theorem bound2447 : BoxMajorant Geometry.b2447 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2447 2 (by decide +kernel) x hx hd ho).elim

theorem bound2094 : BoxMajorant Geometry.b2094 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2094.Widths)
  · have he : Geometry.b2094.half 1 false=Geometry.b2447 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2447
  · have he : Geometry.b2094.half 1 true=Geometry.b2448 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2448

theorem bound2093 : BoxMajorant Geometry.b2093 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2093 2 (by decide +kernel) x hx hd ho).elim

theorem bound1446 : BoxMajorant Geometry.b1446 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1446.Widths)
  · have he : Geometry.b1446.half 0 false=Geometry.b2093 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2093
  · have he : Geometry.b1446.half 0 true=Geometry.b2094 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2094

theorem bound1445 : BoxMajorant Geometry.b1445 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1445 2 (by decide +kernel) x hx hd ho).elim

theorem bound1032 : BoxMajorant Geometry.b1032 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1032.Widths)
  · have he : Geometry.b1032.half 2 false=Geometry.b1445 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1445
  · have he : Geometry.b1032.half 2 true=Geometry.b1446 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1446

theorem bound1031 : BoxMajorant Geometry.b1031 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1031 2 (by decide +kernel) x hx hd ho).elim

theorem bound750 : BoxMajorant Geometry.b750 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b750.Widths)
  · have he : Geometry.b750.half 1 false=Geometry.b1031 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1031
  · have he : Geometry.b750.half 1 true=Geometry.b1032 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1032

end N7.Kernel.Cover
