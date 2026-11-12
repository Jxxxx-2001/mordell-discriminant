import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.PositiveGroups.G0377
import N7.Kernel.PositiveGroups.G0403
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4850 : BoxMajorant Geometry.b4850 := by
  exact PositiveLeaves.L2015.bound

theorem bound4849 : BoxMajorant Geometry.b4849 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4849 2 (by decide +kernel) x hx hd ho).elim

theorem bound4848 : BoxMajorant Geometry.b4848 := by
  exact PositiveLeaves.L2019.bound

theorem bound4847 : BoxMajorant Geometry.b4847 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4847 2 (by decide +kernel) x hx hd ho).elim

theorem bound4540 : BoxMajorant Geometry.b4540 := by
  exact PositiveLeaves.L2014.bound

theorem bound4539 : BoxMajorant Geometry.b4539 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4539.Widths)
  · have he : Geometry.b4539.half 2 false=Geometry.b4849 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4849
  · have he : Geometry.b4539.half 2 true=Geometry.b4850 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4850

theorem bound4538 : BoxMajorant Geometry.b4538 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4538.Widths)
  · have he : Geometry.b4538.half 2 false=Geometry.b4847 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4847
  · have he : Geometry.b4538.half 2 true=Geometry.b4848 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4848

theorem bound4537 : BoxMajorant Geometry.b4537 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4537 2 (by decide +kernel) x hx hd ho).elim

theorem bound4246 : BoxMajorant Geometry.b4246 := by
  exact PositiveLeaves.L2013.bound

theorem bound4245 : BoxMajorant Geometry.b4245 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4245.Widths)
  · have he : Geometry.b4245.half 1 false=Geometry.b4539 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4539
  · have he : Geometry.b4245.half 1 true=Geometry.b4540 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4540

theorem bound4244 : BoxMajorant Geometry.b4244 := by
  exact PositiveLeaves.L2018.bound

theorem bound4243 : BoxMajorant Geometry.b4243 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4243.Widths)
  · have he : Geometry.b4243.half 1 false=Geometry.b4537 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4537
  · have he : Geometry.b4243.half 1 true=Geometry.b4538 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4538

theorem bound3876 : BoxMajorant Geometry.b3876 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3876.Widths)
  · have he : Geometry.b3876.half 0 false=Geometry.b4245 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4245
  · have he : Geometry.b3876.half 0 true=Geometry.b4246 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4246

theorem bound3875 : BoxMajorant Geometry.b3875 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3875 2 (by decide +kernel) x hx hd ho).elim

theorem bound3874 : BoxMajorant Geometry.b3874 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3874.Widths)
  · have he : Geometry.b3874.half 0 false=Geometry.b4243 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4243
  · have he : Geometry.b3874.half 0 true=Geometry.b4244 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4244

theorem bound3873 : BoxMajorant Geometry.b3873 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3873 2 (by decide +kernel) x hx hd ho).elim

theorem bound3552 : BoxMajorant Geometry.b3552 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3552.Widths)
  · have he : Geometry.b3552.half 2 false=Geometry.b3875 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3875
  · have he : Geometry.b3552.half 2 true=Geometry.b3876 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3876

theorem bound3551 : BoxMajorant Geometry.b3551 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3551.Widths)
  · have he : Geometry.b3551.half 2 false=Geometry.b3873 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3873
  · have he : Geometry.b3551.half 2 true=Geometry.b3874 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3874

theorem bound3276 : BoxMajorant Geometry.b3276 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3276.Widths)
  · have he : Geometry.b3276.half 1 false=Geometry.b3551 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3551
  · have he : Geometry.b3276.half 1 true=Geometry.b3552 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3552

theorem bound3275 : BoxMajorant Geometry.b3275 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3275 2 (by decide +kernel) x hx hd ho).elim

theorem bound2945 : BoxMajorant Geometry.b2945 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2945.Widths)
  · have he : Geometry.b2945.half 0 false=Geometry.b3275 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3275
  · have he : Geometry.b2945.half 0 true=Geometry.b3276 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3276

end N7.Kernel.Cover
