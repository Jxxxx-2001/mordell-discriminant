import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0401
import N7.Kernel.PositiveGroups.G0418
import N7.Kernel.PositiveGroups.G0419
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5190 : BoxMajorant Geometry.b5190 := by
  exact PositiveLeaves.L1758.bound

theorem bound5189 : BoxMajorant Geometry.b5189 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5189 2 (by decide +kernel) x hx hd ho).elim

theorem bound5188 : BoxMajorant Geometry.b5188 := by
  exact PositiveLeaves.L1761.bound

theorem bound5187 : BoxMajorant Geometry.b5187 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5187 2 (by decide +kernel) x hx hd ho).elim

theorem bound4918 : BoxMajorant Geometry.b4918 := by
  exact PositiveLeaves.L1752.bound

theorem bound4917 : BoxMajorant Geometry.b4917 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4917 2 (by decide +kernel) x hx hd ho).elim

theorem bound4916 : BoxMajorant Geometry.b4916 := by
  exact PositiveLeaves.L1754.bound

theorem bound4915 : BoxMajorant Geometry.b4915 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4915 2 (by decide +kernel) x hx hd ho).elim

theorem bound4914 : BoxMajorant Geometry.b4914 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4914.Widths)
  · have he : Geometry.b4914.half 0 false=Geometry.b5189 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5189
  · have he : Geometry.b4914.half 0 true=Geometry.b5190 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5190

theorem bound4913 : BoxMajorant Geometry.b4913 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4913 2 (by decide +kernel) x hx hd ho).elim

theorem bound4912 : BoxMajorant Geometry.b4912 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4912.Widths)
  · have he : Geometry.b4912.half 0 false=Geometry.b5187 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5187
  · have he : Geometry.b4912.half 0 true=Geometry.b5188 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5188

theorem bound4911 : BoxMajorant Geometry.b4911 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4911 2 (by decide +kernel) x hx hd ho).elim

theorem bound4582 : BoxMajorant Geometry.b4582 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4582.Widths)
  · have he : Geometry.b4582.half 2 false=Geometry.b4917 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4917
  · have he : Geometry.b4582.half 2 true=Geometry.b4918 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4918

theorem bound4581 : BoxMajorant Geometry.b4581 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4581.Widths)
  · have he : Geometry.b4581.half 2 false=Geometry.b4915 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4915
  · have he : Geometry.b4581.half 2 true=Geometry.b4916 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4916

theorem bound4580 : BoxMajorant Geometry.b4580 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4580.Widths)
  · have he : Geometry.b4580.half 2 false=Geometry.b4913 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4913
  · have he : Geometry.b4580.half 2 true=Geometry.b4914 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4914

theorem bound4579 : BoxMajorant Geometry.b4579 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4579.Widths)
  · have he : Geometry.b4579.half 2 false=Geometry.b4911 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4911
  · have he : Geometry.b4579.half 2 true=Geometry.b4912 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4912

theorem bound4314 : BoxMajorant Geometry.b4314 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4314.Widths)
  · have he : Geometry.b4314.half 1 false=Geometry.b4581 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4581
  · have he : Geometry.b4314.half 1 true=Geometry.b4582 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4582

theorem bound4313 : BoxMajorant Geometry.b4313 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4313 2 (by decide +kernel) x hx hd ho).elim

theorem bound4312 : BoxMajorant Geometry.b4312 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4312.Widths)
  · have he : Geometry.b4312.half 1 false=Geometry.b4579 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4579
  · have he : Geometry.b4312.half 1 true=Geometry.b4580 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4580

theorem bound4311 : BoxMajorant Geometry.b4311 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4311 2 (by decide +kernel) x hx hd ho).elim

theorem bound3960 : BoxMajorant Geometry.b3960 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3960.Widths)
  · have he : Geometry.b3960.half 0 false=Geometry.b4313 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4313
  · have he : Geometry.b3960.half 0 true=Geometry.b4314 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4314

theorem bound3959 : BoxMajorant Geometry.b3959 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3959 2 (by decide +kernel) x hx hd ho).elim

theorem bound3958 : BoxMajorant Geometry.b3958 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3958.Widths)
  · have he : Geometry.b3958.half 0 false=Geometry.b4311 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4311
  · have he : Geometry.b3958.half 0 true=Geometry.b4312 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4312

theorem bound3957 : BoxMajorant Geometry.b3957 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3957 2 (by decide +kernel) x hx hd ho).elim

theorem bound3602 : BoxMajorant Geometry.b3602 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3602.Widths)
  · have he : Geometry.b3602.half 2 false=Geometry.b3959 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3959
  · have he : Geometry.b3602.half 2 true=Geometry.b3960 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3960

theorem bound3601 : BoxMajorant Geometry.b3601 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3601.Widths)
  · have he : Geometry.b3601.half 2 false=Geometry.b3957 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3957
  · have he : Geometry.b3601.half 2 true=Geometry.b3958 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3958

theorem bound3332 : BoxMajorant Geometry.b3332 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3332.Widths)
  · have he : Geometry.b3332.half 1 false=Geometry.b3601 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3601
  · have he : Geometry.b3332.half 1 true=Geometry.b3602 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3602

theorem bound3331 : BoxMajorant Geometry.b3331 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3331 2 (by decide +kernel) x hx hd ho).elim

theorem bound2996 : BoxMajorant Geometry.b2996 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2996.Widths)
  · have he : Geometry.b2996.half 0 false=Geometry.b3331 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3331
  · have he : Geometry.b2996.half 0 true=Geometry.b3332 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3332

end N7.Kernel.Cover
