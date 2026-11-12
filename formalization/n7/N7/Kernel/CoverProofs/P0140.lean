import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0029
import N7.Kernel.CoverGeometry.G0037
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.PositiveGroups.G0200
import N7.Kernel.PositiveGroups.G0201
import N7.Kernel.PositiveGroups.G0241
import N7.Kernel.PositiveGroups.G0242
import N7.Kernel.PositiveGroups.G0243
import N7.Kernel.PositiveGroups.G0278
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3116 : BoxMajorant Geometry.b3116 := by
  exact PositiveLeaves.L707.bound

theorem bound3115 : BoxMajorant Geometry.b3115 := by
  exact PositiveLeaves.L708.bound

theorem bound2726 : BoxMajorant Geometry.b2726 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2726.Widths)
  · have he : Geometry.b2726.half 2 false=Geometry.b3115 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3115
  · have he : Geometry.b2726.half 2 true=Geometry.b3116 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3116

theorem bound2725 : BoxMajorant Geometry.b2725 := by
  exact PositiveLeaves.L709.bound

theorem bound2724 : BoxMajorant Geometry.b2724 := by
  exact PositiveLeaves.L714.bound

theorem bound2723 : BoxMajorant Geometry.b2723 := by
  exact PositiveLeaves.L715.bound

theorem bound2386 : BoxMajorant Geometry.b2386 := by
  exact PositiveLeaves.L706.bound

theorem bound2385 : BoxMajorant Geometry.b2385 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2385.Widths)
  · have he : Geometry.b2385.half 1 false=Geometry.b2725 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2725
  · have he : Geometry.b2385.half 1 true=Geometry.b2726 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2726

theorem bound2384 : BoxMajorant Geometry.b2384 := by
  exact PositiveLeaves.L711.bound

theorem bound2383 : BoxMajorant Geometry.b2383 := by
  exact PositiveLeaves.L712.bound

theorem bound2382 : BoxMajorant Geometry.b2382 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2382.Widths)
  · have he : Geometry.b2382.half 1 false=Geometry.b2723 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2723
  · have he : Geometry.b2382.half 1 true=Geometry.b2724 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2724

theorem bound2381 : BoxMajorant Geometry.b2381 := by
  exact PositiveLeaves.L716.bound

theorem bound1916 : BoxMajorant Geometry.b1916 := by
  exact PositiveLeaves.L703.bound

theorem bound1915 : BoxMajorant Geometry.b1915 := by
  exact PositiveLeaves.L704.bound

theorem bound1914 : BoxMajorant Geometry.b1914 := by
  exact PositiveLeaves.L705.bound

theorem bound1913 : BoxMajorant Geometry.b1913 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1913.Widths)
  · have he : Geometry.b1913.half 0 false=Geometry.b2385 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2385
  · have he : Geometry.b1913.half 0 true=Geometry.b2386 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2386

theorem bound1912 : BoxMajorant Geometry.b1912 := by
  exact PositiveLeaves.L710.bound

theorem bound1911 : BoxMajorant Geometry.b1911 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1911.Widths)
  · have he : Geometry.b1911.half 0 false=Geometry.b2383 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2383
  · have he : Geometry.b1911.half 0 true=Geometry.b2384 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2384

theorem bound1910 : BoxMajorant Geometry.b1910 := by
  exact PositiveLeaves.L713.bound

theorem bound1909 : BoxMajorant Geometry.b1909 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1909.Widths)
  · have he : Geometry.b1909.half 0 false=Geometry.b2381 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2381
  · have he : Geometry.b1909.half 0 true=Geometry.b2382 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2382

theorem bound1324 : BoxMajorant Geometry.b1324 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1324.Widths)
  · have he : Geometry.b1324.half 2 false=Geometry.b1915 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1915
  · have he : Geometry.b1324.half 2 true=Geometry.b1916 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1916

theorem bound1323 : BoxMajorant Geometry.b1323 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1323.Widths)
  · have he : Geometry.b1323.half 2 false=Geometry.b1913 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1913
  · have he : Geometry.b1323.half 2 true=Geometry.b1914 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1914

theorem bound1322 : BoxMajorant Geometry.b1322 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1322.Widths)
  · have he : Geometry.b1322.half 2 false=Geometry.b1911 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1911
  · have he : Geometry.b1322.half 2 true=Geometry.b1912 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1912

theorem bound1321 : BoxMajorant Geometry.b1321 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1321.Widths)
  · have he : Geometry.b1321.half 2 false=Geometry.b1909 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1909
  · have he : Geometry.b1321.half 2 true=Geometry.b1910 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1910

theorem bound950 : BoxMajorant Geometry.b950 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b950.Widths)
  · have he : Geometry.b950.half 1 false=Geometry.b1323 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1323
  · have he : Geometry.b950.half 1 true=Geometry.b1324 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1324

theorem bound949 : BoxMajorant Geometry.b949 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b949.Widths)
  · have he : Geometry.b949.half 1 false=Geometry.b1321 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1321
  · have he : Geometry.b949.half 1 true=Geometry.b1322 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1322

theorem bound659 : BoxMajorant Geometry.b659 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b659.Widths)
  · have he : Geometry.b659.half 0 false=Geometry.b949 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound949
  · have he : Geometry.b659.half 0 true=Geometry.b950 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound950

end N7.Kernel.Cover
