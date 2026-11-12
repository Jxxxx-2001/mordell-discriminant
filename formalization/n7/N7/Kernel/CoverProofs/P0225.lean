import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.PositiveGroups.G0265
import N7.Kernel.PositiveGroups.G0316
import N7.Kernel.PositiveGroups.G0345
import N7.Kernel.PositiveGroups.G0346
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4868 : BoxMajorant Geometry.b4868 := by
  exact PositiveLeaves.L1947.bound

theorem bound4867 : BoxMajorant Geometry.b4867 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4867 2 (by decide +kernel) x hx hd ho).elim

theorem bound4552 : BoxMajorant Geometry.b4552 := by
  exact PositiveLeaves.L1946.bound

theorem bound4551 : BoxMajorant Geometry.b4551 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4551.Widths)
  · have he : Geometry.b4551.half 2 false=Geometry.b4867 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4867
  · have he : Geometry.b4551.half 2 true=Geometry.b4868 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4868

theorem bound4270 : BoxMajorant Geometry.b4270 := by
  exact PositiveLeaves.L1943.bound

theorem bound4269 : BoxMajorant Geometry.b4269 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4269 2 (by decide +kernel) x hx hd ho).elim

theorem bound4268 : BoxMajorant Geometry.b4268 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4268.Widths)
  · have he : Geometry.b4268.half 1 false=Geometry.b4551 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4551
  · have he : Geometry.b4268.half 1 true=Geometry.b4552 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4552

theorem bound4267 : BoxMajorant Geometry.b4267 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4267 2 (by decide +kernel) x hx hd ho).elim

theorem bound3904 : BoxMajorant Geometry.b3904 := by
  exact PositiveLeaves.L1942.bound

theorem bound3903 : BoxMajorant Geometry.b3903 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3903.Widths)
  · have he : Geometry.b3903.half 0 false=Geometry.b4269 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4269
  · have he : Geometry.b3903.half 0 true=Geometry.b4270 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4270

theorem bound3902 : BoxMajorant Geometry.b3902 := by
  exact PositiveLeaves.L1945.bound

theorem bound3901 : BoxMajorant Geometry.b3901 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3901.Widths)
  · have he : Geometry.b3901.half 0 false=Geometry.b4267 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4267
  · have he : Geometry.b3901.half 0 true=Geometry.b4268 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4268

theorem bound3570 : BoxMajorant Geometry.b3570 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3570.Widths)
  · have he : Geometry.b3570.half 2 false=Geometry.b3903 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3903
  · have he : Geometry.b3570.half 2 true=Geometry.b3904 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3904

theorem bound3569 : BoxMajorant Geometry.b3569 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3569.Widths)
  · have he : Geometry.b3569.half 2 false=Geometry.b3901 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3901
  · have he : Geometry.b3569.half 2 true=Geometry.b3902 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3902

theorem bound3292 : BoxMajorant Geometry.b3292 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3292.Widths)
  · have he : Geometry.b3292.half 1 false=Geometry.b3569 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3569
  · have he : Geometry.b3292.half 1 true=Geometry.b3570 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3570

theorem bound3291 : BoxMajorant Geometry.b3291 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3291 2 (by decide +kernel) x hx hd ho).elim

theorem bound2956 : BoxMajorant Geometry.b2956 := by
  exact PositiveLeaves.L1941.bound

theorem bound2955 : BoxMajorant Geometry.b2955 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2955.Widths)
  · have he : Geometry.b2955.half 0 false=Geometry.b3291 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3291
  · have he : Geometry.b2955.half 0 true=Geometry.b3292 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3292

theorem bound2591 : BoxMajorant Geometry.b2591 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2591.Widths)
  · have he : Geometry.b2591.half 2 false=Geometry.b2955 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2955
  · have he : Geometry.b2591.half 2 true=Geometry.b2956 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2956

end N7.Kernel.Cover
