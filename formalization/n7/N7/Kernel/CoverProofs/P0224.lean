import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.PositiveGroups.G0293
import N7.Kernel.PositiveGroups.G0346
import N7.Kernel.PositiveGroups.G0347
import N7.Kernel.PositiveGroups.G0378
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4266 : BoxMajorant Geometry.b4266 := by
  exact PositiveLeaves.L1954.bound

theorem bound4265 : BoxMajorant Geometry.b4265 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4265 2 (by decide +kernel) x hx hd ho).elim

theorem bound3900 : BoxMajorant Geometry.b3900 := by
  exact PositiveLeaves.L1953.bound

theorem bound3899 : BoxMajorant Geometry.b3899 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3899.Widths)
  · have he : Geometry.b3899.half 0 false=Geometry.b4265 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4265
  · have he : Geometry.b3899.half 0 true=Geometry.b4266 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4266

theorem bound3898 : BoxMajorant Geometry.b3898 := by
  exact PositiveLeaves.L1957.bound

theorem bound3897 : BoxMajorant Geometry.b3897 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3897 2 (by decide +kernel) x hx hd ho).elim

theorem bound3568 : BoxMajorant Geometry.b3568 := by
  exact PositiveLeaves.L1952.bound

theorem bound3567 : BoxMajorant Geometry.b3567 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3567.Widths)
  · have he : Geometry.b3567.half 2 false=Geometry.b3899 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3899
  · have he : Geometry.b3567.half 2 true=Geometry.b3900 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3900

theorem bound3566 : BoxMajorant Geometry.b3566 := by
  exact PositiveLeaves.L1956.bound

theorem bound3565 : BoxMajorant Geometry.b3565 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3565.Widths)
  · have he : Geometry.b3565.half 2 false=Geometry.b3897 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3897
  · have he : Geometry.b3565.half 2 true=Geometry.b3898 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3898

theorem bound3290 : BoxMajorant Geometry.b3290 := by
  exact PositiveLeaves.L1951.bound

theorem bound3289 : BoxMajorant Geometry.b3289 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3289.Widths)
  · have he : Geometry.b3289.half 1 false=Geometry.b3567 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3567
  · have he : Geometry.b3289.half 1 true=Geometry.b3568 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3568

theorem bound3288 : BoxMajorant Geometry.b3288 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3288.Widths)
  · have he : Geometry.b3288.half 1 false=Geometry.b3565 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3565
  · have he : Geometry.b3288.half 1 true=Geometry.b3566 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3566

theorem bound3287 : BoxMajorant Geometry.b3287 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3287 2 (by decide +kernel) x hx hd ho).elim

theorem bound2954 : BoxMajorant Geometry.b2954 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2954.Widths)
  · have he : Geometry.b2954.half 0 false=Geometry.b3289 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3289
  · have he : Geometry.b2954.half 0 true=Geometry.b3290 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3290

theorem bound2953 : BoxMajorant Geometry.b2953 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2953.Widths)
  · have he : Geometry.b2953.half 0 false=Geometry.b3287 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3287
  · have he : Geometry.b2953.half 0 true=Geometry.b3288 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3288

theorem bound2590 : BoxMajorant Geometry.b2590 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2590.Widths)
  · have he : Geometry.b2590.half 2 false=Geometry.b2953 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2953
  · have he : Geometry.b2590.half 2 true=Geometry.b2954 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2954

end N7.Kernel.Cover
