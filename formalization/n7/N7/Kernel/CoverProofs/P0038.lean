import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0023
import N7.Kernel.CoverGeometry.G0033
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0044
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverProofs.P0207
import N7.Kernel.CoverProofs.P0208
import N7.Kernel.CoverProofs.P0209
import N7.Kernel.CoverProofs.P0210
import N7.Kernel.PositiveGroups.G0024
import N7.Kernel.PositiveGroups.G0044
import N7.Kernel.PositiveGroups.G0045
import N7.Kernel.PositiveGroups.G0071
import N7.Kernel.PositiveGroups.G0072
import N7.Kernel.PositiveGroups.G0105
import N7.Kernel.PositiveGroups.G0106
import N7.Kernel.PositiveGroups.G0146
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3225 : BoxMajorant Geometry.b3225 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3225 2 (by decide +kernel) x hx hd ho).elim

theorem bound3223 : BoxMajorant Geometry.b3223 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3223 2 (by decide +kernel) x hx hd ho).elim

theorem bound2868 : BoxMajorant Geometry.b2868 := by
  exact PositiveLeaves.L2473.bound

theorem bound2866 : BoxMajorant Geometry.b2866 := by
  exact PositiveLeaves.L2478.bound

theorem bound2864 : BoxMajorant Geometry.b2864 := by
  exact PositiveLeaves.L2484.bound

theorem bound2863 : BoxMajorant Geometry.b2863 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2863.Widths)
  · have he : Geometry.b2863.half 0 false=Geometry.b3225 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3225
  · have he : Geometry.b2863.half 0 true=Geometry.b3226 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3226

theorem bound2862 : BoxMajorant Geometry.b2862 := by
  exact PositiveLeaves.L2490.bound

theorem bound2861 : BoxMajorant Geometry.b2861 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2861.Widths)
  · have he : Geometry.b2861.half 0 false=Geometry.b3223 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3223
  · have he : Geometry.b2861.half 0 true=Geometry.b3224 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3224

theorem bound2514 : BoxMajorant Geometry.b2514 := by
  exact PositiveLeaves.L2472.bound

theorem bound2513 : BoxMajorant Geometry.b2513 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2513.Widths)
  · have he : Geometry.b2513.half 2 false=Geometry.b2867 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2867
  · have he : Geometry.b2513.half 2 true=Geometry.b2868 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2868

theorem bound2512 : BoxMajorant Geometry.b2512 := by
  exact PositiveLeaves.L2477.bound

theorem bound2511 : BoxMajorant Geometry.b2511 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2511.Widths)
  · have he : Geometry.b2511.half 2 false=Geometry.b2865 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2865
  · have he : Geometry.b2511.half 2 true=Geometry.b2866 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2866

theorem bound2510 : BoxMajorant Geometry.b2510 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2510.Widths)
  · have he : Geometry.b2510.half 2 false=Geometry.b2863 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2863
  · have he : Geometry.b2510.half 2 true=Geometry.b2864 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2864

theorem bound2509 : BoxMajorant Geometry.b2509 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2509.Widths)
  · have he : Geometry.b2509.half 2 false=Geometry.b2861 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2861
  · have he : Geometry.b2509.half 2 true=Geometry.b2862 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2862

theorem bound2158 : BoxMajorant Geometry.b2158 := by
  exact PositiveLeaves.L2469.bound

theorem bound2157 : BoxMajorant Geometry.b2157 := by
  exact PositiveLeaves.L2470.bound

theorem bound2156 : BoxMajorant Geometry.b2156 := by
  exact PositiveLeaves.L2471.bound

theorem bound2155 : BoxMajorant Geometry.b2155 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2155.Widths)
  · have he : Geometry.b2155.half 1 false=Geometry.b2513 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2513
  · have he : Geometry.b2155.half 1 true=Geometry.b2514 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2514

theorem bound2154 : BoxMajorant Geometry.b2154 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2154.Widths)
  · have he : Geometry.b2154.half 1 false=Geometry.b2511 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2511
  · have he : Geometry.b2154.half 1 true=Geometry.b2512 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2512

theorem bound2153 : BoxMajorant Geometry.b2153 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2153.Widths)
  · have he : Geometry.b2153.half 1 false=Geometry.b2509 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2509
  · have he : Geometry.b2153.half 1 true=Geometry.b2510 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2510

theorem bound1516 : BoxMajorant Geometry.b1516 := by
  exact PositiveLeaves.L2465.bound

theorem bound1515 : BoxMajorant Geometry.b1515 := by
  exact PositiveLeaves.L2466.bound

theorem bound1514 : BoxMajorant Geometry.b1514 := by
  exact PositiveLeaves.L2467.bound

theorem bound1513 : BoxMajorant Geometry.b1513 := by
  exact PositiveLeaves.L2468.bound

theorem bound1512 : BoxMajorant Geometry.b1512 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1512.Widths)
  · have he : Geometry.b1512.half 0 false=Geometry.b2157 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2157
  · have he : Geometry.b1512.half 0 true=Geometry.b2158 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2158

theorem bound1511 : BoxMajorant Geometry.b1511 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1511.Widths)
  · have he : Geometry.b1511.half 0 false=Geometry.b2155 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2155
  · have he : Geometry.b1511.half 0 true=Geometry.b2156 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2156

theorem bound1510 : BoxMajorant Geometry.b1510 := by
  exact PositiveLeaves.L2476.bound

theorem bound1509 : BoxMajorant Geometry.b1509 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1509.Widths)
  · have he : Geometry.b1509.half 0 false=Geometry.b2153 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2153
  · have he : Geometry.b1509.half 0 true=Geometry.b2154 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2154

theorem bound1074 : BoxMajorant Geometry.b1074 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1074.Widths)
  · have he : Geometry.b1074.half 2 false=Geometry.b1515 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1515
  · have he : Geometry.b1074.half 2 true=Geometry.b1516 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1516

theorem bound1073 : BoxMajorant Geometry.b1073 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1073.Widths)
  · have he : Geometry.b1073.half 2 false=Geometry.b1513 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1513
  · have he : Geometry.b1073.half 2 true=Geometry.b1514 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1514

theorem bound1072 : BoxMajorant Geometry.b1072 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1072.Widths)
  · have he : Geometry.b1072.half 2 false=Geometry.b1511 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1511
  · have he : Geometry.b1072.half 2 true=Geometry.b1512 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1512

theorem bound1071 : BoxMajorant Geometry.b1071 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1071.Widths)
  · have he : Geometry.b1071.half 2 false=Geometry.b1509 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1509
  · have he : Geometry.b1071.half 2 true=Geometry.b1510 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1510

theorem bound776 : BoxMajorant Geometry.b776 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b776.Widths)
  · have he : Geometry.b776.half 1 false=Geometry.b1073 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1073
  · have he : Geometry.b776.half 1 true=Geometry.b1074 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1074

theorem bound775 : BoxMajorant Geometry.b775 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b775.Widths)
  · have he : Geometry.b775.half 1 false=Geometry.b1071 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1071
  · have he : Geometry.b775.half 1 true=Geometry.b1072 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1072

theorem bound498 : BoxMajorant Geometry.b498 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b498.Widths)
  · have he : Geometry.b498.half 0 false=Geometry.b775 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound775
  · have he : Geometry.b498.half 0 true=Geometry.b776 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound776

end N7.Kernel.Cover
