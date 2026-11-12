import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.CoverProofs.P0380
import N7.Kernel.PositiveGroups.G0289
import N7.Kernel.PositiveGroups.G0312
import N7.Kernel.PositiveGroups.G0339
import N7.Kernel.PositiveGroups.G0369
import N7.Kernel.PositiveGroups.G0370
import N7.Kernel.PositiveGroups.G0399
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5210 : BoxMajorant Geometry.b5210 := by
  exact PositiveLeaves.L1679.bound

theorem bound5209 : BoxMajorant Geometry.b5209 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5209 2 (by decide +kernel) x hx hd ho).elim

theorem bound4964 : BoxMajorant Geometry.b4964 := by
  exact PositiveLeaves.L1670.bound

theorem bound4962 : BoxMajorant Geometry.b4962 := by
  exact PositiveLeaves.L1673.bound

theorem bound4961 : BoxMajorant Geometry.b4961 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4961 2 (by decide +kernel) x hx hd ho).elim

theorem bound4960 : BoxMajorant Geometry.b4960 := by
  exact PositiveLeaves.L1678.bound

theorem bound4959 : BoxMajorant Geometry.b4959 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4959.Widths)
  · have he : Geometry.b4959.half 0 false=Geometry.b5209 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5209
  · have he : Geometry.b4959.half 0 true=Geometry.b5210 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5210

theorem bound4958 : BoxMajorant Geometry.b4958 := by
  exact PositiveLeaves.L1681.bound

theorem bound4957 : BoxMajorant Geometry.b4957 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4957 2 (by decide +kernel) x hx hd ho).elim

theorem bound4956 : BoxMajorant Geometry.b4956 := by
  exact PositiveLeaves.L1683.bound

theorem bound4955 : BoxMajorant Geometry.b4955 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4955 2 (by decide +kernel) x hx hd ho).elim

theorem bound4612 : BoxMajorant Geometry.b4612 := by
  exact PositiveLeaves.L1669.bound

theorem bound4611 : BoxMajorant Geometry.b4611 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4611.Widths)
  · have he : Geometry.b4611.half 2 false=Geometry.b4963 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4963
  · have he : Geometry.b4611.half 2 true=Geometry.b4964 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4964

theorem bound4610 : BoxMajorant Geometry.b4610 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4610.Widths)
  · have he : Geometry.b4610.half 2 false=Geometry.b4961 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4961
  · have he : Geometry.b4610.half 2 true=Geometry.b4962 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4962

theorem bound4609 : BoxMajorant Geometry.b4609 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4609 2 (by decide +kernel) x hx hd ho).elim

theorem bound4608 : BoxMajorant Geometry.b4608 := by
  exact PositiveLeaves.L1677.bound

theorem bound4607 : BoxMajorant Geometry.b4607 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4607.Widths)
  · have he : Geometry.b4607.half 2 false=Geometry.b4959 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4959
  · have he : Geometry.b4607.half 2 true=Geometry.b4960 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4960

theorem bound4606 : BoxMajorant Geometry.b4606 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4606.Widths)
  · have he : Geometry.b4606.half 2 false=Geometry.b4957 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4957
  · have he : Geometry.b4606.half 2 true=Geometry.b4958 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4958

theorem bound4605 : BoxMajorant Geometry.b4605 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4605.Widths)
  · have he : Geometry.b4605.half 2 false=Geometry.b4955 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4955
  · have he : Geometry.b4605.half 2 true=Geometry.b4956 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4956

theorem bound4340 : BoxMajorant Geometry.b4340 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4340.Widths)
  · have he : Geometry.b4340.half 1 false=Geometry.b4611 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4611
  · have he : Geometry.b4340.half 1 true=Geometry.b4612 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4612

theorem bound4339 : BoxMajorant Geometry.b4339 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4339.Widths)
  · have he : Geometry.b4339.half 1 false=Geometry.b4609 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4609
  · have he : Geometry.b4339.half 1 true=Geometry.b4610 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4610

theorem bound4338 : BoxMajorant Geometry.b4338 := by
  exact PositiveLeaves.L1676.bound

theorem bound4337 : BoxMajorant Geometry.b4337 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4337.Widths)
  · have he : Geometry.b4337.half 1 false=Geometry.b4607 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4607
  · have he : Geometry.b4337.half 1 true=Geometry.b4608 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4608

theorem bound4336 : BoxMajorant Geometry.b4336 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4336.Widths)
  · have he : Geometry.b4336.half 1 false=Geometry.b4605 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4605
  · have he : Geometry.b4336.half 1 true=Geometry.b4606 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4606

theorem bound4335 : BoxMajorant Geometry.b4335 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4335 2 (by decide +kernel) x hx hd ho).elim

theorem bound3980 : BoxMajorant Geometry.b3980 := by
  exact PositiveLeaves.L1668.bound

theorem bound3979 : BoxMajorant Geometry.b3979 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3979.Widths)
  · have he : Geometry.b3979.half 0 false=Geometry.b4339 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4339
  · have he : Geometry.b3979.half 0 true=Geometry.b4340 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4340

theorem bound3978 : BoxMajorant Geometry.b3978 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3978.Widths)
  · have he : Geometry.b3978.half 0 false=Geometry.b4337 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4337
  · have he : Geometry.b3978.half 0 true=Geometry.b4338 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4338

theorem bound3977 : BoxMajorant Geometry.b3977 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3977.Widths)
  · have he : Geometry.b3977.half 0 false=Geometry.b4335 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4335
  · have he : Geometry.b3977.half 0 true=Geometry.b4336 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4336

theorem bound3612 : BoxMajorant Geometry.b3612 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3612.Widths)
  · have he : Geometry.b3612.half 2 false=Geometry.b3979 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3979
  · have he : Geometry.b3612.half 2 true=Geometry.b3980 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3980

theorem bound3611 : BoxMajorant Geometry.b3611 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3611.Widths)
  · have he : Geometry.b3611.half 2 false=Geometry.b3977 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3977
  · have he : Geometry.b3611.half 2 true=Geometry.b3978 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3978

theorem bound3340 : BoxMajorant Geometry.b3340 := by
  exact PositiveLeaves.L1667.bound

theorem bound3339 : BoxMajorant Geometry.b3339 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3339.Widths)
  · have he : Geometry.b3339.half 1 false=Geometry.b3611 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3611
  · have he : Geometry.b3339.half 1 true=Geometry.b3612 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3612

theorem bound3000 : BoxMajorant Geometry.b3000 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3000.Widths)
  · have he : Geometry.b3000.half 0 false=Geometry.b3339 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3339
  · have he : Geometry.b3000.half 0 true=Geometry.b3340 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3340

end N7.Kernel.Cover
