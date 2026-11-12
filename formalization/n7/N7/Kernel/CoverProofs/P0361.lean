import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.PositiveGroups.G0423
import N7.Kernel.PositiveGroups.G0437
import N7.Kernel.PositiveGroups.G0438
import N7.Kernel.PositiveGroups.G0451
import N7.Kernel.PositiveGroups.G0452
import N7.Kernel.PositiveGroups.G0461
import N7.Kernel.PositiveGroups.G0462
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5874 : BoxMajorant Geometry.b5874 := by
  exact PositiveLeaves.L2198.bound

theorem bound5873 : BoxMajorant Geometry.b5873 := by
  exact PositiveLeaves.L2199.bound

theorem bound5836 : BoxMajorant Geometry.b5836 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5836.Widths)
  · have he : Geometry.b5836.half 2 false=Geometry.b5873 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5873
  · have he : Geometry.b5836.half 2 true=Geometry.b5874 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5874

theorem bound5835 : BoxMajorant Geometry.b5835 := by
  exact PositiveLeaves.L2200.bound

theorem bound5804 : BoxMajorant Geometry.b5804 := by
  exact PositiveLeaves.L2197.bound

theorem bound5803 : BoxMajorant Geometry.b5803 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5803.Widths)
  · have he : Geometry.b5803.half 1 false=Geometry.b5835 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5835
  · have he : Geometry.b5803.half 1 true=Geometry.b5836 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5836

theorem bound5742 : BoxMajorant Geometry.b5742 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5742.Widths)
  · have he : Geometry.b5742.half 0 false=Geometry.b5803 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5803
  · have he : Geometry.b5742.half 0 true=Geometry.b5804 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5804

theorem bound5741 : BoxMajorant Geometry.b5741 := by
  exact PositiveLeaves.L2201.bound

theorem bound5740 : BoxMajorant Geometry.b5740 := by
  exact PositiveLeaves.L2202.bound

theorem bound5739 : BoxMajorant Geometry.b5739 := by
  exact PositiveLeaves.L2203.bound

theorem bound5700 : BoxMajorant Geometry.b5700 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5700.Widths)
  · have he : Geometry.b5700.half 2 false=Geometry.b5741 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5741
  · have he : Geometry.b5700.half 2 true=Geometry.b5742 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5742

theorem bound5699 : BoxMajorant Geometry.b5699 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5699.Widths)
  · have he : Geometry.b5699.half 2 false=Geometry.b5739 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5739
  · have he : Geometry.b5699.half 2 true=Geometry.b5740 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5740

theorem bound5670 : BoxMajorant Geometry.b5670 := by
  exact PositiveLeaves.L2196.bound

theorem bound5669 : BoxMajorant Geometry.b5669 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5669.Widths)
  · have he : Geometry.b5669.half 1 false=Geometry.b5699 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5699
  · have he : Geometry.b5669.half 1 true=Geometry.b5700 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5700

theorem bound5626 : BoxMajorant Geometry.b5626 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5626.Widths)
  · have he : Geometry.b5626.half 0 false=Geometry.b5669 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5669
  · have he : Geometry.b5626.half 0 true=Geometry.b5670 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5670

end N7.Kernel.Cover
