import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverProofs.P0249
import N7.Kernel.CoverProofs.P0250
import N7.Kernel.CoverProofs.P0251
import N7.Kernel.CoverProofs.P0252
import N7.Kernel.CoverProofs.P0253
import N7.Kernel.PositiveGroups.G0068
import N7.Kernel.PositiveGroups.G0145
import N7.Kernel.PositiveGroups.G0182
import N7.Kernel.PositiveGroups.G0226
import N7.Kernel.PositiveGroups.G0262
import N7.Kernel.PositiveGroups.G0263
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3591 : BoxMajorant Geometry.b3591 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3591 2 (by decide +kernel) x hx hd ho).elim

theorem bound3326 : BoxMajorant Geometry.b3326 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3326.Widths)
  · have he : Geometry.b3326.half 1 false=Geometry.b3593 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3593
  · have he : Geometry.b3326.half 1 true=Geometry.b3594 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3594

theorem bound3325 : BoxMajorant Geometry.b3325 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3325.Widths)
  · have he : Geometry.b3325.half 1 false=Geometry.b3591 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3591
  · have he : Geometry.b3325.half 1 true=Geometry.b3592 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3592

theorem bound3324 : BoxMajorant Geometry.b3324 := by
  exact PositiveLeaves.L1826.bound

theorem bound3323 : BoxMajorant Geometry.b3323 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3323 2 (by decide +kernel) x hx hd ho).elim

theorem bound3322 : BoxMajorant Geometry.b3322 := by
  exact PositiveLeaves.L1829.bound

theorem bound3321 : BoxMajorant Geometry.b3321 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3321 2 (by decide +kernel) x hx hd ho).elim

theorem bound2992 : BoxMajorant Geometry.b2992 := by
  exact PositiveLeaves.L1783.bound

theorem bound2991 : BoxMajorant Geometry.b2991 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2991.Widths)
  · have he : Geometry.b2991.half 0 false=Geometry.b3327 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3327
  · have he : Geometry.b2991.half 0 true=Geometry.b3328 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3328

theorem bound2990 : BoxMajorant Geometry.b2990 := by
  exact PositiveLeaves.L1810.bound

theorem bound2989 : BoxMajorant Geometry.b2989 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2989.Widths)
  · have he : Geometry.b2989.half 0 false=Geometry.b3325 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3325
  · have he : Geometry.b2989.half 0 true=Geometry.b3326 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3326

theorem bound2988 : BoxMajorant Geometry.b2988 := by
  exact PositiveLeaves.L1825.bound

theorem bound2987 : BoxMajorant Geometry.b2987 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2987.Widths)
  · have he : Geometry.b2987.half 0 false=Geometry.b3323 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3323
  · have he : Geometry.b2987.half 0 true=Geometry.b3324 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3324

theorem bound2986 : BoxMajorant Geometry.b2986 := by
  exact PositiveLeaves.L1828.bound

theorem bound2985 : BoxMajorant Geometry.b2985 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2985.Widths)
  · have he : Geometry.b2985.half 0 false=Geometry.b3321 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3321
  · have he : Geometry.b2985.half 0 true=Geometry.b3322 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3322

theorem bound2610 : BoxMajorant Geometry.b2610 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2610.Widths)
  · have he : Geometry.b2610.half 2 false=Geometry.b2991 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2991
  · have he : Geometry.b2610.half 2 true=Geometry.b2992 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2992

theorem bound2609 : BoxMajorant Geometry.b2609 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2609.Widths)
  · have he : Geometry.b2609.half 2 false=Geometry.b2989 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2989
  · have he : Geometry.b2609.half 2 true=Geometry.b2990 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2990

theorem bound2608 : BoxMajorant Geometry.b2608 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2608.Widths)
  · have he : Geometry.b2608.half 2 false=Geometry.b2987 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2987
  · have he : Geometry.b2608.half 2 true=Geometry.b2988 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2988

theorem bound2607 : BoxMajorant Geometry.b2607 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2607.Widths)
  · have he : Geometry.b2607.half 2 false=Geometry.b2985 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2985
  · have he : Geometry.b2607.half 2 true=Geometry.b2986 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2986

theorem bound2242 : BoxMajorant Geometry.b2242 := by
  exact PositiveLeaves.L1782.bound

theorem bound2241 : BoxMajorant Geometry.b2241 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2241.Widths)
  · have he : Geometry.b2241.half 1 false=Geometry.b2609 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2609
  · have he : Geometry.b2241.half 1 true=Geometry.b2610 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2610

theorem bound2240 : BoxMajorant Geometry.b2240 := by
  exact PositiveLeaves.L1824.bound

theorem bound2239 : BoxMajorant Geometry.b2239 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2239.Widths)
  · have he : Geometry.b2239.half 1 false=Geometry.b2607 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2607
  · have he : Geometry.b2239.half 1 true=Geometry.b2608 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2608

theorem bound1626 : BoxMajorant Geometry.b1626 := by
  exact PositiveLeaves.L1781.bound

theorem bound1625 : BoxMajorant Geometry.b1625 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1625.Widths)
  · have he : Geometry.b1625.half 0 false=Geometry.b2241 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2241
  · have he : Geometry.b1625.half 0 true=Geometry.b2242 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2242

theorem bound1624 : BoxMajorant Geometry.b1624 := by
  exact PositiveLeaves.L1823.bound

theorem bound1623 : BoxMajorant Geometry.b1623 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1623.Widths)
  · have he : Geometry.b1623.half 0 false=Geometry.b2239 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2239
  · have he : Geometry.b1623.half 0 true=Geometry.b2240 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2240

theorem bound1150 : BoxMajorant Geometry.b1150 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1150.Widths)
  · have he : Geometry.b1150.half 2 false=Geometry.b1625 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1625
  · have he : Geometry.b1150.half 2 true=Geometry.b1626 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1626

theorem bound1149 : BoxMajorant Geometry.b1149 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1149.Widths)
  · have he : Geometry.b1149.half 2 false=Geometry.b1623 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1623
  · have he : Geometry.b1149.half 2 true=Geometry.b1624 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1624

theorem bound834 : BoxMajorant Geometry.b834 := by
  exact PositiveLeaves.L1780.bound

theorem bound833 : BoxMajorant Geometry.b833 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b833.Widths)
  · have he : Geometry.b833.half 1 false=Geometry.b1149 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1149
  · have he : Geometry.b833.half 1 true=Geometry.b1150 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1150

theorem bound556 : BoxMajorant Geometry.b556 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b556.Widths)
  · have he : Geometry.b556.half 0 false=Geometry.b833 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound833
  · have he : Geometry.b556.half 0 true=Geometry.b834 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound834

end N7.Kernel.Cover
