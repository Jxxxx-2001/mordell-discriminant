import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0029
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.CoverGeometry.G0037
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.PositiveGroups.G0157
import N7.Kernel.PositiveGroups.G0207
import N7.Kernel.PositiveGroups.G0245
import N7.Kernel.PositiveGroups.G0246
import N7.Kernel.PositiveGroups.G0247
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2720 : BoxMajorant Geometry.b2720 := by
  exact PositiveLeaves.L758.bound

theorem bound2719 : BoxMajorant Geometry.b2719 := by
  exact PositiveLeaves.L759.bound

theorem bound2368 : BoxMajorant Geometry.b2368 := by
  exact PositiveLeaves.L755.bound

theorem bound2367 : BoxMajorant Geometry.b2367 := by
  exact PositiveLeaves.L756.bound

theorem bound2366 : BoxMajorant Geometry.b2366 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2366.Widths)
  · have he : Geometry.b2366.half 1 false=Geometry.b2719 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2719
  · have he : Geometry.b2366.half 1 true=Geometry.b2720 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2720

theorem bound2365 : BoxMajorant Geometry.b2365 := by
  exact PositiveLeaves.L760.bound

theorem bound1886 : BoxMajorant Geometry.b1886 := by
  exact PositiveLeaves.L752.bound

theorem bound1885 : BoxMajorant Geometry.b1885 := by
  exact PositiveLeaves.L753.bound

theorem bound1884 : BoxMajorant Geometry.b1884 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1884.Widths)
  · have he : Geometry.b1884.half 0 false=Geometry.b2367 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2367
  · have he : Geometry.b1884.half 0 true=Geometry.b2368 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2368

theorem bound1883 : BoxMajorant Geometry.b1883 := by
  exact PositiveLeaves.L757.bound

theorem bound1882 : BoxMajorant Geometry.b1882 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1882.Widths)
  · have he : Geometry.b1882.half 0 false=Geometry.b2365 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2365
  · have he : Geometry.b1882.half 0 true=Geometry.b2366 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2366

theorem bound1881 : BoxMajorant Geometry.b1881 := by
  exact PositiveLeaves.L761.bound

theorem bound1308 : BoxMajorant Geometry.b1308 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1308.Widths)
  · have he : Geometry.b1308.half 2 false=Geometry.b1885 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1885
  · have he : Geometry.b1308.half 2 true=Geometry.b1886 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1886

theorem bound1307 : BoxMajorant Geometry.b1307 := by
  exact PositiveLeaves.L754.bound

theorem bound1306 : BoxMajorant Geometry.b1306 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1306.Widths)
  · have he : Geometry.b1306.half 2 false=Geometry.b1883 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1883
  · have he : Geometry.b1306.half 2 true=Geometry.b1884 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1884

theorem bound1305 : BoxMajorant Geometry.b1305 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1305.Widths)
  · have he : Geometry.b1305.half 2 false=Geometry.b1881 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1881
  · have he : Geometry.b1305.half 2 true=Geometry.b1882 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1882

theorem bound942 : BoxMajorant Geometry.b942 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b942.Widths)
  · have he : Geometry.b942.half 1 false=Geometry.b1307 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1307
  · have he : Geometry.b942.half 1 true=Geometry.b1308 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1308

theorem bound941 : BoxMajorant Geometry.b941 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b941.Widths)
  · have he : Geometry.b941.half 1 false=Geometry.b1305 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1305
  · have he : Geometry.b941.half 1 true=Geometry.b1306 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1306

theorem bound650 : BoxMajorant Geometry.b650 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b650.Widths)
  · have he : Geometry.b650.half 0 false=Geometry.b941 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound941
  · have he : Geometry.b650.half 0 true=Geometry.b942 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound942

end N7.Kernel.Cover
