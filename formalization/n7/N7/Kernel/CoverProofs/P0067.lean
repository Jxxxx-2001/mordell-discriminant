import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverProofs.P0212
import N7.Kernel.CoverProofs.P0213
import N7.Kernel.CoverProofs.P0214
import N7.Kernel.PositiveGroups.G0024
import N7.Kernel.PositiveGroups.G0043
import N7.Kernel.PositiveGroups.G0069
import N7.Kernel.PositiveGroups.G0104
import N7.Kernel.PositiveGroups.G0105
import N7.Kernel.PositiveGroups.G0146
import N7.Kernel.PositiveGroups.G0183
import N7.Kernel.PositiveGroups.G0227
import N7.Kernel.PositiveGroups.G0228
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3818 : BoxMajorant Geometry.b3818 := by
  exact PositiveLeaves.L2223.bound

theorem bound3817 : BoxMajorant Geometry.b3817 := by
  exact PositiveLeaves.L2224.bound

theorem bound3522 : BoxMajorant Geometry.b3522 := by
  exact PositiveLeaves.L2173.bound

theorem bound3518 : BoxMajorant Geometry.b3518 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3518.Widths)
  · have he : Geometry.b3518.half 2 false=Geometry.b3817 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3817
  · have he : Geometry.b3518.half 2 true=Geometry.b3818 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3818

theorem bound3517 : BoxMajorant Geometry.b3517 := by
  exact PositiveLeaves.L2225.bound

theorem bound3246 : BoxMajorant Geometry.b3246 := by
  exact PositiveLeaves.L2172.bound

theorem bound3245 : BoxMajorant Geometry.b3245 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3245.Widths)
  · have he : Geometry.b3245.half 1 false=Geometry.b3521 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3521
  · have he : Geometry.b3245.half 1 true=Geometry.b3522 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3522

theorem bound3244 : BoxMajorant Geometry.b3244 := by
  exact PositiveLeaves.L2181.bound

theorem bound3243 : BoxMajorant Geometry.b3243 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3243.Widths)
  · have he : Geometry.b3243.half 1 false=Geometry.b3519 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3519
  · have he : Geometry.b3243.half 1 true=Geometry.b3520 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3520

theorem bound3242 : BoxMajorant Geometry.b3242 := by
  exact PositiveLeaves.L2222.bound

theorem bound3241 : BoxMajorant Geometry.b3241 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3241.Widths)
  · have he : Geometry.b3241.half 1 false=Geometry.b3517 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3517
  · have he : Geometry.b3241.half 1 true=Geometry.b3518 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3518

theorem bound2918 : BoxMajorant Geometry.b2918 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2918.Widths)
  · have he : Geometry.b2918.half 0 false=Geometry.b3245 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3245
  · have he : Geometry.b2918.half 0 true=Geometry.b3246 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3246

theorem bound2917 : BoxMajorant Geometry.b2917 := by
  exact PositiveLeaves.L2178.bound

theorem bound2916 : BoxMajorant Geometry.b2916 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2916.Widths)
  · have he : Geometry.b2916.half 0 false=Geometry.b3243 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3243
  · have he : Geometry.b2916.half 0 true=Geometry.b3244 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3244

theorem bound2915 : BoxMajorant Geometry.b2915 := by
  exact PositiveLeaves.L2221.bound

theorem bound2914 : BoxMajorant Geometry.b2914 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2914.Widths)
  · have he : Geometry.b2914.half 0 false=Geometry.b3241 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3241
  · have he : Geometry.b2914.half 0 true=Geometry.b3242 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3242

theorem bound2913 : BoxMajorant Geometry.b2913 := by
  exact PositiveLeaves.L2226.bound

theorem bound2570 : BoxMajorant Geometry.b2570 := by
  exact PositiveLeaves.L2171.bound

theorem bound2569 : BoxMajorant Geometry.b2569 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2569.Widths)
  · have he : Geometry.b2569.half 2 false=Geometry.b2917 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2917
  · have he : Geometry.b2569.half 2 true=Geometry.b2918 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2918

theorem bound2568 : BoxMajorant Geometry.b2568 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2568.Widths)
  · have he : Geometry.b2568.half 2 false=Geometry.b2915 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2915
  · have he : Geometry.b2568.half 2 true=Geometry.b2916 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2916

theorem bound2567 : BoxMajorant Geometry.b2567 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2567.Widths)
  · have he : Geometry.b2567.half 2 false=Geometry.b2913 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2913
  · have he : Geometry.b2567.half 2 true=Geometry.b2914 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2914

theorem bound2208 : BoxMajorant Geometry.b2208 := by
  exact PositiveLeaves.L2170.bound

theorem bound2207 : BoxMajorant Geometry.b2207 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2207.Widths)
  · have he : Geometry.b2207.half 1 false=Geometry.b2569 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2569
  · have he : Geometry.b2207.half 1 true=Geometry.b2570 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2570

theorem bound2206 : BoxMajorant Geometry.b2206 := by
  exact PositiveLeaves.L2180.bound

theorem bound2205 : BoxMajorant Geometry.b2205 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2205.Widths)
  · have he : Geometry.b2205.half 1 false=Geometry.b2567 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2567
  · have he : Geometry.b2205.half 1 true=Geometry.b2568 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2568

theorem bound1604 : BoxMajorant Geometry.b1604 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1604.Widths)
  · have he : Geometry.b1604.half 0 false=Geometry.b2207 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2207
  · have he : Geometry.b1604.half 0 true=Geometry.b2208 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2208

theorem bound1603 : BoxMajorant Geometry.b1603 := by
  exact PositiveLeaves.L2179.bound

theorem bound1602 : BoxMajorant Geometry.b1602 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1602.Widths)
  · have he : Geometry.b1602.half 0 false=Geometry.b2205 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2205
  · have he : Geometry.b1602.half 0 true=Geometry.b2206 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2206

theorem bound1601 : BoxMajorant Geometry.b1601 := by
  exact PositiveLeaves.L2227.bound

theorem bound1138 : BoxMajorant Geometry.b1138 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1138.Widths)
  · have he : Geometry.b1138.half 2 false=Geometry.b1603 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1603
  · have he : Geometry.b1138.half 2 true=Geometry.b1604 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1604

theorem bound1137 : BoxMajorant Geometry.b1137 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1137.Widths)
  · have he : Geometry.b1137.half 2 false=Geometry.b1601 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1601
  · have he : Geometry.b1137.half 2 true=Geometry.b1602 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1602

theorem bound826 : BoxMajorant Geometry.b826 := by
  exact PositiveLeaves.L2169.bound

theorem bound825 : BoxMajorant Geometry.b825 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b825.Widths)
  · have he : Geometry.b825.half 1 false=Geometry.b1137 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1137
  · have he : Geometry.b825.half 1 true=Geometry.b1138 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1138

theorem bound546 : BoxMajorant Geometry.b546 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b546.Widths)
  · have he : Geometry.b546.half 0 false=Geometry.b825 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound825
  · have he : Geometry.b546.half 0 true=Geometry.b826 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound826

end N7.Kernel.Cover
