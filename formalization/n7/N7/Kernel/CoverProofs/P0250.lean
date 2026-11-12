import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0343
import N7.Kernel.PositiveGroups.G0374
import N7.Kernel.PositiveGroups.G0420
import N7.Kernel.PositiveGroups.G0436
import N7.Kernel.PositiveGroups.G0437
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5184 : BoxMajorant Geometry.b5184 := by
  exact PositiveLeaves.L1786.bound

theorem bound5183 : BoxMajorant Geometry.b5183 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5183 2 (by decide +kernel) x hx hd ho).elim

theorem bound5182 : BoxMajorant Geometry.b5182 := by
  exact PositiveLeaves.L1789.bound

theorem bound5181 : BoxMajorant Geometry.b5181 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5181 2 (by decide +kernel) x hx hd ho).elim

theorem bound5180 : BoxMajorant Geometry.b5180 := by
  exact PositiveLeaves.L1791.bound

theorem bound5179 : BoxMajorant Geometry.b5179 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5179 2 (by decide +kernel) x hx hd ho).elim

theorem bound4908 : BoxMajorant Geometry.b4908 := by
  exact PositiveLeaves.L1785.bound

theorem bound4907 : BoxMajorant Geometry.b4907 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4907.Widths)
  · have he : Geometry.b4907.half 0 false=Geometry.b5183 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5183
  · have he : Geometry.b4907.half 0 true=Geometry.b5184 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5184

theorem bound4906 : BoxMajorant Geometry.b4906 := by
  exact PositiveLeaves.L1788.bound

theorem bound4905 : BoxMajorant Geometry.b4905 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4905.Widths)
  · have he : Geometry.b4905.half 0 false=Geometry.b5181 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5181
  · have he : Geometry.b4905.half 0 true=Geometry.b5182 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5182

theorem bound4904 : BoxMajorant Geometry.b4904 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4904.Widths)
  · have he : Geometry.b4904.half 0 false=Geometry.b5179 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5179
  · have he : Geometry.b4904.half 0 true=Geometry.b5180 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5180

theorem bound4903 : BoxMajorant Geometry.b4903 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4903 2 (by decide +kernel) x hx hd ho).elim

theorem bound4576 : BoxMajorant Geometry.b4576 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4576.Widths)
  · have he : Geometry.b4576.half 2 false=Geometry.b4907 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4907
  · have he : Geometry.b4576.half 2 true=Geometry.b4908 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4908

theorem bound4575 : BoxMajorant Geometry.b4575 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4575.Widths)
  · have he : Geometry.b4575.half 2 false=Geometry.b4905 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4905
  · have he : Geometry.b4575.half 2 true=Geometry.b4906 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4906

theorem bound4574 : BoxMajorant Geometry.b4574 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4574.Widths)
  · have he : Geometry.b4574.half 2 false=Geometry.b4903 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4903
  · have he : Geometry.b4574.half 2 true=Geometry.b4904 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4904

theorem bound4573 : BoxMajorant Geometry.b4573 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4573 2 (by decide +kernel) x hx hd ho).elim

theorem bound4308 : BoxMajorant Geometry.b4308 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4308.Widths)
  · have he : Geometry.b4308.half 1 false=Geometry.b4575 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4575
  · have he : Geometry.b4308.half 1 true=Geometry.b4576 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4576

theorem bound4307 : BoxMajorant Geometry.b4307 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4307.Widths)
  · have he : Geometry.b4307.half 1 false=Geometry.b4573 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4573
  · have he : Geometry.b4307.half 1 true=Geometry.b4574 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4574

theorem bound4306 : BoxMajorant Geometry.b4306 := by
  exact PositiveLeaves.L1796.bound

theorem bound4305 : BoxMajorant Geometry.b4305 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4305 2 (by decide +kernel) x hx hd ho).elim

theorem bound3954 : BoxMajorant Geometry.b3954 := by
  exact PositiveLeaves.L1784.bound

theorem bound3953 : BoxMajorant Geometry.b3953 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3953.Widths)
  · have he : Geometry.b3953.half 0 false=Geometry.b4307 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4307
  · have he : Geometry.b3953.half 0 true=Geometry.b4308 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4308

theorem bound3952 : BoxMajorant Geometry.b3952 := by
  exact PositiveLeaves.L1795.bound

theorem bound3951 : BoxMajorant Geometry.b3951 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3951.Widths)
  · have he : Geometry.b3951.half 0 false=Geometry.b4305 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4305
  · have he : Geometry.b3951.half 0 true=Geometry.b4306 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4306

theorem bound3598 : BoxMajorant Geometry.b3598 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3598.Widths)
  · have he : Geometry.b3598.half 2 false=Geometry.b3953 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3953
  · have he : Geometry.b3598.half 2 true=Geometry.b3954 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3954

theorem bound3597 : BoxMajorant Geometry.b3597 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3597.Widths)
  · have he : Geometry.b3597.half 2 false=Geometry.b3951 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3951
  · have he : Geometry.b3597.half 2 true=Geometry.b3952 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3952

theorem bound3328 : BoxMajorant Geometry.b3328 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3328.Widths)
  · have he : Geometry.b3328.half 1 false=Geometry.b3597 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3597
  · have he : Geometry.b3328.half 1 true=Geometry.b3598 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3598

end N7.Kernel.Cover
