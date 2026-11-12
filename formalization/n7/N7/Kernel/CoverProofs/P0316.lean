import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.PositiveGroups.G0301
import N7.Kernel.PositiveGroups.G0325
import N7.Kernel.PositiveGroups.G0355
import N7.Kernel.PositiveGroups.G0387
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4094 : BoxMajorant Geometry.b4094 := by
  exact PositiveLeaves.L663.bound

theorem bound4093 : BoxMajorant Geometry.b4093 := by
  exact PositiveLeaves.L664.bound

theorem bound4092 : BoxMajorant Geometry.b4092 := by
  exact PositiveLeaves.L665.bound

theorem bound4091 : BoxMajorant Geometry.b4091 := by
  exact PositiveLeaves.L666.bound

theorem bound3692 : BoxMajorant Geometry.b3692 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3692.Widths)
  · have he : Geometry.b3692.half 2 false=Geometry.b4093 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4093
  · have he : Geometry.b3692.half 2 true=Geometry.b4094 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4094

theorem bound3691 : BoxMajorant Geometry.b3691 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3691.Widths)
  · have he : Geometry.b3691.half 2 false=Geometry.b4091 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4091
  · have he : Geometry.b3691.half 2 true=Geometry.b4092 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4092

theorem bound3690 : BoxMajorant Geometry.b3690 := by
  exact PositiveLeaves.L667.bound

theorem bound3689 : BoxMajorant Geometry.b3689 := by
  exact PositiveLeaves.L668.bound

theorem bound3424 : BoxMajorant Geometry.b3424 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3424.Widths)
  · have he : Geometry.b3424.half 1 false=Geometry.b3691 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3691
  · have he : Geometry.b3424.half 1 true=Geometry.b3692 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3692

theorem bound3423 : BoxMajorant Geometry.b3423 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3423.Widths)
  · have he : Geometry.b3423.half 1 false=Geometry.b3689 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3689
  · have he : Geometry.b3423.half 1 true=Geometry.b3690 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3690

theorem bound3134 : BoxMajorant Geometry.b3134 := by
  exact PositiveLeaves.L662.bound

theorem bound3133 : BoxMajorant Geometry.b3133 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3133.Widths)
  · have he : Geometry.b3133.half 0 false=Geometry.b3423 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3423
  · have he : Geometry.b3133.half 0 true=Geometry.b3424 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3424

theorem bound2739 : BoxMajorant Geometry.b2739 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2739.Widths)
  · have he : Geometry.b2739.half 2 false=Geometry.b3133 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3133
  · have he : Geometry.b2739.half 2 true=Geometry.b3134 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3134

end N7.Kernel.Cover
