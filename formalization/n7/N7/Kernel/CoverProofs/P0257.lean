import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.PositiveGroups.G0338
import N7.Kernel.PositiveGroups.G0367
import N7.Kernel.PositiveGroups.G0368
import N7.Kernel.PositiveGroups.G0398
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4972 : BoxMajorant Geometry.b4972 := by
  exact PositiveLeaves.L1615.bound

theorem bound4971 : BoxMajorant Geometry.b4971 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4971 2 (by decide +kernel) x hx hd ho).elim

theorem bound4622 : BoxMajorant Geometry.b4622 := by
  exact PositiveLeaves.L1614.bound

theorem bound4621 : BoxMajorant Geometry.b4621 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4621.Widths)
  · have he : Geometry.b4621.half 2 false=Geometry.b4971 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4971
  · have he : Geometry.b4621.half 2 true=Geometry.b4972 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4972

theorem bound4356 : BoxMajorant Geometry.b4356 := by
  exact PositiveLeaves.L1613.bound

theorem bound4355 : BoxMajorant Geometry.b4355 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4355.Widths)
  · have he : Geometry.b4355.half 1 false=Geometry.b4621 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4621
  · have he : Geometry.b4355.half 1 true=Geometry.b4622 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4622

theorem bound4002 : BoxMajorant Geometry.b4002 := by
  exact PositiveLeaves.L1611.bound

theorem bound4001 : BoxMajorant Geometry.b4001 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4001 2 (by decide +kernel) x hx hd ho).elim

theorem bound4000 : BoxMajorant Geometry.b4000 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4000.Widths)
  · have he : Geometry.b4000.half 0 false=Geometry.b4355 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4355
  · have he : Geometry.b4000.half 0 true=Geometry.b4356 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4356

theorem bound3999 : BoxMajorant Geometry.b3999 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3999 2 (by decide +kernel) x hx hd ho).elim

theorem bound3628 : BoxMajorant Geometry.b3628 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3628.Widths)
  · have he : Geometry.b3628.half 2 false=Geometry.b4001 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4001
  · have he : Geometry.b3628.half 2 true=Geometry.b4002 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4002

theorem bound3627 : BoxMajorant Geometry.b3627 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3627.Widths)
  · have he : Geometry.b3627.half 2 false=Geometry.b3999 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3999
  · have he : Geometry.b3627.half 2 true=Geometry.b4000 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4000

theorem bound3354 : BoxMajorant Geometry.b3354 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3354.Widths)
  · have he : Geometry.b3354.half 1 false=Geometry.b3627 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3627
  · have he : Geometry.b3354.half 1 true=Geometry.b3628 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3628

theorem bound3353 : BoxMajorant Geometry.b3353 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3353 2 (by decide +kernel) x hx hd ho).elim

theorem bound3012 : BoxMajorant Geometry.b3012 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3012.Widths)
  · have he : Geometry.b3012.half 0 false=Geometry.b3353 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3353
  · have he : Geometry.b3012.half 0 true=Geometry.b3354 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3354

theorem bound3011 : BoxMajorant Geometry.b3011 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3011 2 (by decide +kernel) x hx hd ho).elim

theorem bound2620 : BoxMajorant Geometry.b2620 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2620.Widths)
  · have he : Geometry.b2620.half 2 false=Geometry.b3011 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3011
  · have he : Geometry.b2620.half 2 true=Geometry.b3012 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3012

end N7.Kernel.Cover
