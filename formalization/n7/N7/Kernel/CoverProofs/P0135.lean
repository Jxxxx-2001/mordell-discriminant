import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0029
import N7.Kernel.PositiveGroups.G0206
import N7.Kernel.PositiveGroups.G0207
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1880 : BoxMajorant Geometry.b1880 := by
  exact PositiveLeaves.L763.bound

theorem bound1879 : BoxMajorant Geometry.b1879 := by
  exact PositiveLeaves.L764.bound

theorem bound1878 : BoxMajorant Geometry.b1878 := by
  exact PositiveLeaves.L765.bound

theorem bound1877 : BoxMajorant Geometry.b1877 := by
  exact PositiveLeaves.L766.bound

theorem bound1876 : BoxMajorant Geometry.b1876 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1876 3 (by decide +kernel) x hx hd ho).elim

theorem bound1875 : BoxMajorant Geometry.b1875 := by
  exact PositiveLeaves.L768.bound

theorem bound1874 : BoxMajorant Geometry.b1874 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1874 3 (by decide +kernel) x hx hd ho).elim

theorem bound1873 : BoxMajorant Geometry.b1873 := by
  exact PositiveLeaves.L770.bound

theorem bound1304 : BoxMajorant Geometry.b1304 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1304.Widths)
  · have he : Geometry.b1304.half 2 false=Geometry.b1879 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1879
  · have he : Geometry.b1304.half 2 true=Geometry.b1880 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1880

theorem bound1303 : BoxMajorant Geometry.b1303 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1303.Widths)
  · have he : Geometry.b1303.half 2 false=Geometry.b1877 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1877
  · have he : Geometry.b1303.half 2 true=Geometry.b1878 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1878

theorem bound1302 : BoxMajorant Geometry.b1302 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1302.Widths)
  · have he : Geometry.b1302.half 2 false=Geometry.b1875 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1875
  · have he : Geometry.b1302.half 2 true=Geometry.b1876 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1876

theorem bound1301 : BoxMajorant Geometry.b1301 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1301.Widths)
  · have he : Geometry.b1301.half 2 false=Geometry.b1873 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1873
  · have he : Geometry.b1301.half 2 true=Geometry.b1874 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1874

theorem bound940 : BoxMajorant Geometry.b940 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b940.Widths)
  · have he : Geometry.b940.half 1 false=Geometry.b1303 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1303
  · have he : Geometry.b940.half 1 true=Geometry.b1304 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1304

theorem bound939 : BoxMajorant Geometry.b939 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b939.Widths)
  · have he : Geometry.b939.half 1 false=Geometry.b1301 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1301
  · have he : Geometry.b939.half 1 true=Geometry.b1302 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1302

theorem bound648 : BoxMajorant Geometry.b648 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b648.Widths)
  · have he : Geometry.b648.half 0 false=Geometry.b939 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound939
  · have he : Geometry.b648.half 0 true=Geometry.b940 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound940

end N7.Kernel.Cover
