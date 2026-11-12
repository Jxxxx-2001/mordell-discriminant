import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.PositiveGroups.G0264
import N7.Kernel.PositiveGroups.G0291
import N7.Kernel.PositiveGroups.G0292
import N7.Kernel.PositiveGroups.G0315
import N7.Kernel.PositiveGroups.G0375
import N7.Kernel.PositiveGroups.G0376
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4858 : BoxMajorant Geometry.b4858 := by
  exact PositiveLeaves.L1996.bound

theorem bound4857 : BoxMajorant Geometry.b4857 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4857 2 (by decide +kernel) x hx hd ho).elim

theorem bound4856 : BoxMajorant Geometry.b4856 := by
  exact PositiveLeaves.L1998.bound

theorem bound4855 : BoxMajorant Geometry.b4855 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4855 2 (by decide +kernel) x hx hd ho).elim

theorem bound4854 : BoxMajorant Geometry.b4854 := by
  exact PositiveLeaves.L2002.bound

theorem bound4853 : BoxMajorant Geometry.b4853 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4853 2 (by decide +kernel) x hx hd ho).elim

theorem bound4852 : BoxMajorant Geometry.b4852 := by
  exact PositiveLeaves.L2004.bound

theorem bound4851 : BoxMajorant Geometry.b4851 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4851 2 (by decide +kernel) x hx hd ho).elim

theorem bound4544 : BoxMajorant Geometry.b4544 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4544.Widths)
  · have he : Geometry.b4544.half 2 false=Geometry.b4857 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4857
  · have he : Geometry.b4544.half 2 true=Geometry.b4858 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4858

theorem bound4543 : BoxMajorant Geometry.b4543 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4543.Widths)
  · have he : Geometry.b4543.half 2 false=Geometry.b4855 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4855
  · have he : Geometry.b4543.half 2 true=Geometry.b4856 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4856

theorem bound4542 : BoxMajorant Geometry.b4542 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4542.Widths)
  · have he : Geometry.b4542.half 2 false=Geometry.b4853 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4853
  · have he : Geometry.b4542.half 2 true=Geometry.b4854 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4854

theorem bound4541 : BoxMajorant Geometry.b4541 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4541.Widths)
  · have he : Geometry.b4541.half 2 false=Geometry.b4851 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4851
  · have he : Geometry.b4541.half 2 true=Geometry.b4852 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4852

theorem bound4254 : BoxMajorant Geometry.b4254 := by
  exact PositiveLeaves.L1995.bound

theorem bound4253 : BoxMajorant Geometry.b4253 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4253.Widths)
  · have he : Geometry.b4253.half 1 false=Geometry.b4543 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4543
  · have he : Geometry.b4253.half 1 true=Geometry.b4544 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4544

theorem bound4252 : BoxMajorant Geometry.b4252 := by
  exact PositiveLeaves.L2001.bound

theorem bound4251 : BoxMajorant Geometry.b4251 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4251.Widths)
  · have he : Geometry.b4251.half 1 false=Geometry.b4541 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4541
  · have he : Geometry.b4251.half 1 true=Geometry.b4542 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4542

theorem bound3884 : BoxMajorant Geometry.b3884 := by
  exact PositiveLeaves.L1994.bound

theorem bound3883 : BoxMajorant Geometry.b3883 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3883.Widths)
  · have he : Geometry.b3883.half 0 false=Geometry.b4253 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4253
  · have he : Geometry.b3883.half 0 true=Geometry.b4254 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4254

theorem bound3882 : BoxMajorant Geometry.b3882 := by
  exact PositiveLeaves.L2000.bound

theorem bound3881 : BoxMajorant Geometry.b3881 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3881.Widths)
  · have he : Geometry.b3881.half 0 false=Geometry.b4251 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4251
  · have he : Geometry.b3881.half 0 true=Geometry.b4252 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4252

theorem bound3556 : BoxMajorant Geometry.b3556 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3556.Widths)
  · have he : Geometry.b3556.half 2 false=Geometry.b3883 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3883
  · have he : Geometry.b3556.half 2 true=Geometry.b3884 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3884

theorem bound3555 : BoxMajorant Geometry.b3555 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3555.Widths)
  · have he : Geometry.b3555.half 2 false=Geometry.b3881 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3881
  · have he : Geometry.b3555.half 2 true=Geometry.b3882 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3882

theorem bound3280 : BoxMajorant Geometry.b3280 := by
  exact PositiveLeaves.L1993.bound

theorem bound3279 : BoxMajorant Geometry.b3279 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3279.Widths)
  · have he : Geometry.b3279.half 1 false=Geometry.b3555 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3555
  · have he : Geometry.b3279.half 1 true=Geometry.b3556 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3556

theorem bound2947 : BoxMajorant Geometry.b2947 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2947.Widths)
  · have he : Geometry.b2947.half 0 false=Geometry.b3279 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3279
  · have he : Geometry.b2947.half 0 true=Geometry.b3280 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3280

end N7.Kernel.Cover
