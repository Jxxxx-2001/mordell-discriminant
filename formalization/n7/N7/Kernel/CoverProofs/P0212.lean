import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0228
import N7.Kernel.PositiveGroups.G0266
import N7.Kernel.PositiveGroups.G0296
import N7.Kernel.PositiveGroups.G0319
import N7.Kernel.PositiveGroups.G0320
import N7.Kernel.PositiveGroups.G0351
import N7.Kernel.PositiveGroups.G0352
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5470 : BoxMajorant Geometry.b5470 := by
  exact PositiveLeaves.L2214.bound

theorem bound5469 : BoxMajorant Geometry.b5469 := by
  exact PositiveLeaves.L2215.bound

theorem bound5340 : BoxMajorant Geometry.b5340 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5340.Widths)
  · have he : Geometry.b5340.half 2 false=Geometry.b5469 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5469
  · have he : Geometry.b5340.half 2 true=Geometry.b5470 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5470

theorem bound5339 : BoxMajorant Geometry.b5339 := by
  exact PositiveLeaves.L2216.bound

theorem bound5156 : BoxMajorant Geometry.b5156 := by
  exact PositiveLeaves.L2213.bound

theorem bound5155 : BoxMajorant Geometry.b5155 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5155.Widths)
  · have he : Geometry.b5155.half 1 false=Geometry.b5339 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5339
  · have he : Geometry.b5155.half 1 true=Geometry.b5340 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5340

theorem bound4806 : BoxMajorant Geometry.b4806 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4806.Widths)
  · have he : Geometry.b4806.half 0 false=Geometry.b5155 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5155
  · have he : Geometry.b4806.half 0 true=Geometry.b5156 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5156

theorem bound4805 : BoxMajorant Geometry.b4805 := by
  exact PositiveLeaves.L2217.bound

theorem bound4804 : BoxMajorant Geometry.b4804 := by
  exact PositiveLeaves.L2218.bound

theorem bound4803 : BoxMajorant Geometry.b4803 := by
  exact PositiveLeaves.L2219.bound

theorem bound4512 : BoxMajorant Geometry.b4512 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4512.Widths)
  · have he : Geometry.b4512.half 2 false=Geometry.b4805 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4805
  · have he : Geometry.b4512.half 2 true=Geometry.b4806 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4806

theorem bound4511 : BoxMajorant Geometry.b4511 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4511.Widths)
  · have he : Geometry.b4511.half 2 false=Geometry.b4803 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4803
  · have he : Geometry.b4511.half 2 true=Geometry.b4804 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4804

theorem bound4208 : BoxMajorant Geometry.b4208 := by
  exact PositiveLeaves.L2212.bound

theorem bound4207 : BoxMajorant Geometry.b4207 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4207.Widths)
  · have he : Geometry.b4207.half 1 false=Geometry.b4511 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4511
  · have he : Geometry.b4207.half 1 true=Geometry.b4512 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4512

theorem bound3820 : BoxMajorant Geometry.b3820 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3820.Widths)
  · have he : Geometry.b3820.half 0 false=Geometry.b4207 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4207
  · have he : Geometry.b3820.half 0 true=Geometry.b4208 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4208

theorem bound3819 : BoxMajorant Geometry.b3819 := by
  exact PositiveLeaves.L2220.bound

theorem bound3519 : BoxMajorant Geometry.b3519 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3519.Widths)
  · have he : Geometry.b3519.half 2 false=Geometry.b3819 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3819
  · have he : Geometry.b3519.half 2 true=Geometry.b3820 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3820

end N7.Kernel.Cover
