import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.PositiveGroups.G0294
import N7.Kernel.PositiveGroups.G0350
import N7.Kernel.PositiveGroups.G0380
import N7.Kernel.PositiveGroups.G0381
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4816 : BoxMajorant Geometry.b4816 := by
  exact PositiveLeaves.L2104.bound

theorem bound4815 : BoxMajorant Geometry.b4815 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4815 2 (by decide +kernel) x hx hd ho).elim

theorem bound4520 : BoxMajorant Geometry.b4520 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4520.Widths)
  · have he : Geometry.b4520.half 2 false=Geometry.b4815 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4815
  · have he : Geometry.b4520.half 2 true=Geometry.b4816 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4816

theorem bound4519 : BoxMajorant Geometry.b4519 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4519 2 (by decide +kernel) x hx hd ho).elim

theorem bound4222 : BoxMajorant Geometry.b4222 := by
  exact PositiveLeaves.L2103.bound

theorem bound4221 : BoxMajorant Geometry.b4221 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4221.Widths)
  · have he : Geometry.b4221.half 1 false=Geometry.b4519 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4519
  · have he : Geometry.b4221.half 1 true=Geometry.b4520 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4520

theorem bound4220 : BoxMajorant Geometry.b4220 := by
  exact PositiveLeaves.L2108.bound

theorem bound4219 : BoxMajorant Geometry.b4219 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4219 2 (by decide +kernel) x hx hd ho).elim

theorem bound3850 : BoxMajorant Geometry.b3850 := by
  exact PositiveLeaves.L2102.bound

theorem bound3849 : BoxMajorant Geometry.b3849 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3849.Widths)
  · have he : Geometry.b3849.half 0 false=Geometry.b4221 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4221
  · have he : Geometry.b3849.half 0 true=Geometry.b4222 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4222

theorem bound3848 : BoxMajorant Geometry.b3848 := by
  exact PositiveLeaves.L2107.bound

theorem bound3847 : BoxMajorant Geometry.b3847 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3847.Widths)
  · have he : Geometry.b3847.half 0 false=Geometry.b4219 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4219
  · have he : Geometry.b3847.half 0 true=Geometry.b4220 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4220

theorem bound3538 : BoxMajorant Geometry.b3538 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3538.Widths)
  · have he : Geometry.b3538.half 2 false=Geometry.b3849 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3849
  · have he : Geometry.b3538.half 2 true=Geometry.b3850 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3850

theorem bound3537 : BoxMajorant Geometry.b3537 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3537.Widths)
  · have he : Geometry.b3537.half 2 false=Geometry.b3847 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3847
  · have he : Geometry.b3537.half 2 true=Geometry.b3848 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3848

theorem bound3264 : BoxMajorant Geometry.b3264 := by
  exact PositiveLeaves.L2101.bound

theorem bound3263 : BoxMajorant Geometry.b3263 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3263.Widths)
  · have he : Geometry.b3263.half 1 false=Geometry.b3537 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3537
  · have he : Geometry.b3263.half 1 true=Geometry.b3538 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3538

theorem bound2935 : BoxMajorant Geometry.b2935 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2935.Widths)
  · have he : Geometry.b2935.half 0 false=Geometry.b3263 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3263
  · have he : Geometry.b2935.half 0 true=Geometry.b3264 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3264

end N7.Kernel.Cover
