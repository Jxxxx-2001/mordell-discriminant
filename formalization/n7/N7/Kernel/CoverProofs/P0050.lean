import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.PositiveGroups.G0110
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2522 : BoxMajorant Geometry.b2522 := by
  exact PositiveLeaves.L2429.bound

theorem bound2521 : BoxMajorant Geometry.b2521 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2521 0 (by decide +kernel) x hx hd ho).elim

theorem bound2164 : BoxMajorant Geometry.b2164 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2164 0 (by decide +kernel) x hx hd ho).elim

theorem bound2163 : BoxMajorant Geometry.b2163 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2163.Widths)
  · have he : Geometry.b2163.half 1 false=Geometry.b2521 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2521
  · have he : Geometry.b2163.half 1 true=Geometry.b2522 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2522

theorem bound1530 : BoxMajorant Geometry.b1530 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1530.Widths)
  · have he : Geometry.b1530.half 0 false=Geometry.b2163 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2163
  · have he : Geometry.b1530.half 0 true=Geometry.b2164 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2164

theorem bound1529 : BoxMajorant Geometry.b1529 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1529 2 (by decide +kernel) x hx hd ho).elim

theorem bound1086 : BoxMajorant Geometry.b1086 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1086.Widths)
  · have he : Geometry.b1086.half 2 false=Geometry.b1529 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1529
  · have he : Geometry.b1086.half 2 true=Geometry.b1530 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1530

theorem bound1085 : BoxMajorant Geometry.b1085 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1085 0 (by decide +kernel) x hx hd ho).elim

theorem bound785 : BoxMajorant Geometry.b785 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b785.Widths)
  · have he : Geometry.b785.half 1 false=Geometry.b1085 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1085
  · have he : Geometry.b785.half 1 true=Geometry.b1086 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1086

end N7.Kernel.Cover
