import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.CoverGeometry.G0037
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.PositiveGroups.G0139
import N7.Kernel.PositiveGroups.G0140
import N7.Kernel.PositiveGroups.G0177
import N7.Kernel.PositiveGroups.G0178
import N7.Kernel.PositiveGroups.G0220
import N7.Kernel.PositiveGroups.G0221
import N7.Kernel.PositiveGroups.G0259
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3148 : BoxMajorant Geometry.b3148 := by
  exact PositiveLeaves.L491.bound

theorem bound3147 : BoxMajorant Geometry.b3147 := by
  exact PositiveLeaves.L492.bound

theorem bound3146 : BoxMajorant Geometry.b3146 := by
  exact PositiveLeaves.L495.bound

theorem bound3145 : BoxMajorant Geometry.b3145 := by
  exact PositiveLeaves.L496.bound

theorem bound2756 : BoxMajorant Geometry.b2756 := by
  exact PositiveLeaves.L490.bound

theorem bound2755 : BoxMajorant Geometry.b2755 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2755.Widths)
  · have he : Geometry.b2755.half 2 false=Geometry.b3147 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3147
  · have he : Geometry.b2755.half 2 true=Geometry.b3148 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3148

theorem bound2754 : BoxMajorant Geometry.b2754 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2754.Widths)
  · have he : Geometry.b2754.half 2 false=Geometry.b3145 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3145
  · have he : Geometry.b2754.half 2 true=Geometry.b3146 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3146

theorem bound2753 : BoxMajorant Geometry.b2753 := by
  exact PositiveLeaves.L497.bound

theorem bound2422 : BoxMajorant Geometry.b2422 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2422 0 (by decide +kernel) x hx hd ho).elim

theorem bound2421 : BoxMajorant Geometry.b2421 := by
  exact PositiveLeaves.L488.bound

theorem bound2420 : BoxMajorant Geometry.b2420 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2420.Widths)
  · have he : Geometry.b2420.half 1 false=Geometry.b2755 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2755
  · have he : Geometry.b2420.half 1 true=Geometry.b2756 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2756

theorem bound2419 : BoxMajorant Geometry.b2419 := by
  exact PositiveLeaves.L493.bound

theorem bound2418 : BoxMajorant Geometry.b2418 := by
  exact PositiveLeaves.L494.bound

theorem bound2417 : BoxMajorant Geometry.b2417 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2417.Widths)
  · have he : Geometry.b2417.half 1 false=Geometry.b2753 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2753
  · have he : Geometry.b2417.half 1 true=Geometry.b2754 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2754

theorem bound2020 : BoxMajorant Geometry.b2020 := by
  exact PositiveLeaves.L484.bound

theorem bound2019 : BoxMajorant Geometry.b2019 := by
  exact PositiveLeaves.L485.bound

theorem bound2018 : BoxMajorant Geometry.b2018 := by
  exact PositiveLeaves.L486.bound

theorem bound2017 : BoxMajorant Geometry.b2017 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2017.Widths)
  · have he : Geometry.b2017.half 0 false=Geometry.b2421 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2421
  · have he : Geometry.b2017.half 0 true=Geometry.b2422 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2422

theorem bound2016 : BoxMajorant Geometry.b2016 := by
  exact PositiveLeaves.L489.bound

theorem bound2015 : BoxMajorant Geometry.b2015 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2015.Widths)
  · have he : Geometry.b2015.half 0 false=Geometry.b2419 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2419
  · have he : Geometry.b2015.half 0 true=Geometry.b2420 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2420

theorem bound2014 : BoxMajorant Geometry.b2014 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2014.Widths)
  · have he : Geometry.b2014.half 0 false=Geometry.b2417 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2417
  · have he : Geometry.b2014.half 0 true=Geometry.b2418 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2418

theorem bound2013 : BoxMajorant Geometry.b2013 := by
  exact PositiveLeaves.L498.bound

theorem bound1392 : BoxMajorant Geometry.b1392 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1392.Widths)
  · have he : Geometry.b1392.half 2 false=Geometry.b2019 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2019
  · have he : Geometry.b1392.half 2 true=Geometry.b2020 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2020

theorem bound1391 : BoxMajorant Geometry.b1391 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1391.Widths)
  · have he : Geometry.b1391.half 2 false=Geometry.b2017 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2017
  · have he : Geometry.b1391.half 2 true=Geometry.b2018 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2018

theorem bound1390 : BoxMajorant Geometry.b1390 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1390.Widths)
  · have he : Geometry.b1390.half 2 false=Geometry.b2015 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2015
  · have he : Geometry.b1390.half 2 true=Geometry.b2016 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2016

theorem bound1389 : BoxMajorant Geometry.b1389 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1389.Widths)
  · have he : Geometry.b1389.half 2 false=Geometry.b2013 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2013
  · have he : Geometry.b1389.half 2 true=Geometry.b2014 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2014

theorem bound992 : BoxMajorant Geometry.b992 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b992.Widths)
  · have he : Geometry.b992.half 1 false=Geometry.b1391 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1391
  · have he : Geometry.b992.half 1 true=Geometry.b1392 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1392

theorem bound991 : BoxMajorant Geometry.b991 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b991.Widths)
  · have he : Geometry.b991.half 1 false=Geometry.b1389 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1389
  · have he : Geometry.b991.half 1 true=Geometry.b1390 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1390

theorem bound694 : BoxMajorant Geometry.b694 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b694.Widths)
  · have he : Geometry.b694.half 0 false=Geometry.b991 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound991
  · have he : Geometry.b694.half 0 true=Geometry.b992 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound992

end N7.Kernel.Cover
