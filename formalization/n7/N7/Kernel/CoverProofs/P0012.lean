import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.CoverProofs.P0086
import N7.Kernel.CoverProofs.P0087
import N7.Kernel.CoverProofs.P0088
import N7.Kernel.PositiveGroups.G0003
import N7.Kernel.PositiveGroups.G0006
import N7.Kernel.PositiveGroups.G0007
import N7.Kernel.PositiveGroups.G0013
import N7.Kernel.PositiveGroups.G0014
import N7.Kernel.PositiveGroups.G0028
import N7.Kernel.PositiveGroups.G0048
import N7.Kernel.PositiveGroups.G0077
import N7.Kernel.PositiveGroups.G0116
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1674 : BoxMajorant Geometry.b1674 := by
  exact PositiveLeaves.L1199.bound

theorem bound1673 : BoxMajorant Geometry.b1673 := by
  exact PositiveLeaves.L1200.bound

theorem bound1671 : BoxMajorant Geometry.b1671 := by
  exact PositiveLeaves.L1207.bound

theorem bound1669 : BoxMajorant Geometry.b1669 := by
  exact PositiveLeaves.L1213.bound

theorem bound1667 : BoxMajorant Geometry.b1667 := by
  exact PositiveLeaves.L1233.bound

theorem bound1182 : BoxMajorant Geometry.b1182 := by
  exact PositiveLeaves.L1193.bound

theorem bound1181 : BoxMajorant Geometry.b1181 := by
  exact PositiveLeaves.L1194.bound

theorem bound1180 : BoxMajorant Geometry.b1180 := by
  exact PositiveLeaves.L1195.bound

theorem bound1179 : BoxMajorant Geometry.b1179 := by
  exact PositiveLeaves.L1196.bound

theorem bound1178 : BoxMajorant Geometry.b1178 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1178.Widths)
  · have he : Geometry.b1178.half 2 false=Geometry.b1673 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1673
  · have he : Geometry.b1178.half 2 true=Geometry.b1674 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1674

theorem bound1177 : BoxMajorant Geometry.b1177 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1177.Widths)
  · have he : Geometry.b1177.half 2 false=Geometry.b1671 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1671
  · have he : Geometry.b1177.half 2 true=Geometry.b1672 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1672

theorem bound1176 : BoxMajorant Geometry.b1176 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1176.Widths)
  · have he : Geometry.b1176.half 2 false=Geometry.b1669 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1669
  · have he : Geometry.b1176.half 2 true=Geometry.b1670 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1670

theorem bound1175 : BoxMajorant Geometry.b1175 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1175.Widths)
  · have he : Geometry.b1175.half 2 false=Geometry.b1667 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1667
  · have he : Geometry.b1175.half 2 true=Geometry.b1668 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1668

theorem bound862 : BoxMajorant Geometry.b862 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b862.Widths)
  · have he : Geometry.b862.half 1 false=Geometry.b1181 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1181
  · have he : Geometry.b862.half 1 true=Geometry.b1182 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1182

theorem bound861 : BoxMajorant Geometry.b861 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b861.Widths)
  · have he : Geometry.b861.half 1 false=Geometry.b1179 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1179
  · have he : Geometry.b861.half 1 true=Geometry.b1180 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1180

theorem bound860 : BoxMajorant Geometry.b860 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b860.Widths)
  · have he : Geometry.b860.half 1 false=Geometry.b1177 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1177
  · have he : Geometry.b860.half 1 true=Geometry.b1178 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1178

theorem bound859 : BoxMajorant Geometry.b859 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b859.Widths)
  · have he : Geometry.b859.half 1 false=Geometry.b1175 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1175
  · have he : Geometry.b859.half 1 true=Geometry.b1176 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1176

theorem bound858 : BoxMajorant Geometry.b858 := by
  exact PositiveLeaves.L1234.bound

theorem bound857 : BoxMajorant Geometry.b857 := by
  exact PositiveLeaves.L1235.bound

theorem bound588 : BoxMajorant Geometry.b588 := by
  exact PositiveLeaves.L1192.bound

theorem bound587 : BoxMajorant Geometry.b587 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b587.Widths)
  · have he : Geometry.b587.half 0 false=Geometry.b861 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound861
  · have he : Geometry.b587.half 0 true=Geometry.b862 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound862

theorem bound586 : BoxMajorant Geometry.b586 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b586.Widths)
  · have he : Geometry.b586.half 0 false=Geometry.b859 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound859
  · have he : Geometry.b586.half 0 true=Geometry.b860 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound860

theorem bound585 : BoxMajorant Geometry.b585 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b585.Widths)
  · have he : Geometry.b585.half 0 false=Geometry.b857 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound857
  · have he : Geometry.b585.half 0 true=Geometry.b858 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound858

theorem bound380 : BoxMajorant Geometry.b380 := by
  exact PositiveLeaves.L1191.bound

theorem bound379 : BoxMajorant Geometry.b379 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b379.Widths)
  · have he : Geometry.b379.half 2 false=Geometry.b587 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound587
  · have he : Geometry.b379.half 2 true=Geometry.b588 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound588

theorem bound378 : BoxMajorant Geometry.b378 := by
  exact PositiveLeaves.L1198.bound

theorem bound377 : BoxMajorant Geometry.b377 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b377.Widths)
  · have he : Geometry.b377.half 2 false=Geometry.b585 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound585
  · have he : Geometry.b377.half 2 true=Geometry.b586 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound586

theorem bound246 : BoxMajorant Geometry.b246 := by
  exact PositiveLeaves.L1190.bound

theorem bound245 : BoxMajorant Geometry.b245 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b245.Widths)
  · have he : Geometry.b245.half 1 false=Geometry.b379 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound379
  · have he : Geometry.b245.half 1 true=Geometry.b380 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound380

theorem bound244 : BoxMajorant Geometry.b244 := by
  exact PositiveLeaves.L1197.bound

theorem bound243 : BoxMajorant Geometry.b243 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b243.Widths)
  · have he : Geometry.b243.half 1 false=Geometry.b377 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound377
  · have he : Geometry.b243.half 1 true=Geometry.b378 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound378

theorem bound146 : BoxMajorant Geometry.b146 := by
  exact PositiveLeaves.L1188.bound

theorem bound145 : BoxMajorant Geometry.b145 := by
  exact PositiveLeaves.L1189.bound

theorem bound144 : BoxMajorant Geometry.b144 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b144.Widths)
  · have he : Geometry.b144.half 0 false=Geometry.b245 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound245
  · have he : Geometry.b144.half 0 true=Geometry.b246 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound246

theorem bound143 : BoxMajorant Geometry.b143 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b143.Widths)
  · have he : Geometry.b143.half 0 false=Geometry.b243 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound243
  · have he : Geometry.b143.half 0 true=Geometry.b244 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound244

theorem bound84 : BoxMajorant Geometry.b84 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b84.Widths)
  · have he : Geometry.b84.half 2 false=Geometry.b145 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound145
  · have he : Geometry.b84.half 2 true=Geometry.b146 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound146

theorem bound83 : BoxMajorant Geometry.b83 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b83.Widths)
  · have he : Geometry.b83.half 2 false=Geometry.b143 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound143
  · have he : Geometry.b83.half 2 true=Geometry.b144 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound144

theorem bound45 : BoxMajorant Geometry.b45 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b45.Widths)
  · have he : Geometry.b45.half 1 false=Geometry.b83 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound83
  · have he : Geometry.b45.half 1 true=Geometry.b84 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound84

end N7.Kernel.Cover
