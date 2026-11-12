import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverProofs.P0366
import N7.Kernel.CoverProofs.P0367
import N7.Kernel.CoverProofs.P0368
import N7.Kernel.CoverProofs.P0369
import N7.Kernel.CoverProofs.P0370
import N7.Kernel.PositiveGroups.G0317
import N7.Kernel.PositiveGroups.G0347
import N7.Kernel.PositiveGroups.G0348
import N7.Kernel.PositiveGroups.G0349
import N7.Kernel.PositiveGroups.G0379
import N7.Kernel.PositiveGroups.G0404
import N7.Kernel.PositiveGroups.G0405
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4842 : BoxMajorant Geometry.b4842 := by
  exact PositiveLeaves.L2045.bound

theorem bound4840 : BoxMajorant Geometry.b4840 := by
  exact PositiveLeaves.L2048.bound

theorem bound4837 : BoxMajorant Geometry.b4837 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4837 2 (by decide +kernel) x hx hd ho).elim

theorem bound4836 : BoxMajorant Geometry.b4836 := by
  exact PositiveLeaves.L2055.bound

theorem bound4835 : BoxMajorant Geometry.b4835 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4835 2 (by decide +kernel) x hx hd ho).elim

theorem bound4834 : BoxMajorant Geometry.b4834 := by
  exact PositiveLeaves.L2057.bound

theorem bound4833 : BoxMajorant Geometry.b4833 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4833 2 (by decide +kernel) x hx hd ho).elim

theorem bound4832 : BoxMajorant Geometry.b4832 := by
  exact PositiveLeaves.L2061.bound

theorem bound4831 : BoxMajorant Geometry.b4831 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4831 2 (by decide +kernel) x hx hd ho).elim

theorem bound4830 : BoxMajorant Geometry.b4830 := by
  exact PositiveLeaves.L2063.bound

theorem bound4829 : BoxMajorant Geometry.b4829 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4829 2 (by decide +kernel) x hx hd ho).elim

theorem bound4534 : BoxMajorant Geometry.b4534 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4534.Widths)
  · have he : Geometry.b4534.half 2 false=Geometry.b4841 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4841
  · have he : Geometry.b4534.half 2 true=Geometry.b4842 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4842

theorem bound4533 : BoxMajorant Geometry.b4533 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4533.Widths)
  · have he : Geometry.b4533.half 2 false=Geometry.b4839 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4839
  · have he : Geometry.b4533.half 2 true=Geometry.b4840 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4840

theorem bound4532 : BoxMajorant Geometry.b4532 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4532.Widths)
  · have he : Geometry.b4532.half 2 false=Geometry.b4837 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4837
  · have he : Geometry.b4532.half 2 true=Geometry.b4838 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4838

theorem bound4531 : BoxMajorant Geometry.b4531 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4531 2 (by decide +kernel) x hx hd ho).elim

theorem bound4530 : BoxMajorant Geometry.b4530 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4530.Widths)
  · have he : Geometry.b4530.half 2 false=Geometry.b4835 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4835
  · have he : Geometry.b4530.half 2 true=Geometry.b4836 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4836

theorem bound4529 : BoxMajorant Geometry.b4529 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4529.Widths)
  · have he : Geometry.b4529.half 2 false=Geometry.b4833 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4833
  · have he : Geometry.b4529.half 2 true=Geometry.b4834 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4834

theorem bound4528 : BoxMajorant Geometry.b4528 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4528.Widths)
  · have he : Geometry.b4528.half 2 false=Geometry.b4831 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4831
  · have he : Geometry.b4528.half 2 true=Geometry.b4832 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4832

theorem bound4527 : BoxMajorant Geometry.b4527 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4527.Widths)
  · have he : Geometry.b4527.half 2 false=Geometry.b4829 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4829
  · have he : Geometry.b4527.half 2 true=Geometry.b4830 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4830

theorem bound4236 : BoxMajorant Geometry.b4236 := by
  exact PositiveLeaves.L2038.bound

theorem bound4235 : BoxMajorant Geometry.b4235 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4235.Widths)
  · have he : Geometry.b4235.half 1 false=Geometry.b4535 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4535
  · have he : Geometry.b4235.half 1 true=Geometry.b4536 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4536

theorem bound4234 : BoxMajorant Geometry.b4234 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4234.Widths)
  · have he : Geometry.b4234.half 1 false=Geometry.b4533 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4533
  · have he : Geometry.b4234.half 1 true=Geometry.b4534 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4534

theorem bound4233 : BoxMajorant Geometry.b4233 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4233.Widths)
  · have he : Geometry.b4233.half 1 false=Geometry.b4531 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4531
  · have he : Geometry.b4233.half 1 true=Geometry.b4532 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4532

theorem bound4232 : BoxMajorant Geometry.b4232 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4232.Widths)
  · have he : Geometry.b4232.half 1 false=Geometry.b4529 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4529
  · have he : Geometry.b4232.half 1 true=Geometry.b4530 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4530

theorem bound4231 : BoxMajorant Geometry.b4231 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4231 2 (by decide +kernel) x hx hd ho).elim

theorem bound4230 : BoxMajorant Geometry.b4230 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4230.Widths)
  · have he : Geometry.b4230.half 1 false=Geometry.b4527 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4527
  · have he : Geometry.b4230.half 1 true=Geometry.b4528 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4528

theorem bound4229 : BoxMajorant Geometry.b4229 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4229 2 (by decide +kernel) x hx hd ho).elim

theorem bound3864 : BoxMajorant Geometry.b3864 := by
  exact PositiveLeaves.L2037.bound

theorem bound3863 : BoxMajorant Geometry.b3863 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3863.Widths)
  · have he : Geometry.b3863.half 0 false=Geometry.b4235 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4235
  · have he : Geometry.b3863.half 0 true=Geometry.b4236 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4236

theorem bound3862 : BoxMajorant Geometry.b3862 := by
  exact PositiveLeaves.L2044.bound

theorem bound3861 : BoxMajorant Geometry.b3861 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3861.Widths)
  · have he : Geometry.b3861.half 0 false=Geometry.b4233 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4233
  · have he : Geometry.b3861.half 0 true=Geometry.b4234 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4234

theorem bound3860 : BoxMajorant Geometry.b3860 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3860.Widths)
  · have he : Geometry.b3860.half 0 false=Geometry.b4231 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4231
  · have he : Geometry.b3860.half 0 true=Geometry.b4232 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4232

theorem bound3859 : BoxMajorant Geometry.b3859 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3859 2 (by decide +kernel) x hx hd ho).elim

theorem bound3858 : BoxMajorant Geometry.b3858 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3858.Widths)
  · have he : Geometry.b3858.half 0 false=Geometry.b4229 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4229
  · have he : Geometry.b3858.half 0 true=Geometry.b4230 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4230

theorem bound3857 : BoxMajorant Geometry.b3857 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3857 2 (by decide +kernel) x hx hd ho).elim

theorem bound3546 : BoxMajorant Geometry.b3546 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3546.Widths)
  · have he : Geometry.b3546.half 2 false=Geometry.b3863 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3863
  · have he : Geometry.b3546.half 2 true=Geometry.b3864 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3864

theorem bound3545 : BoxMajorant Geometry.b3545 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3545.Widths)
  · have he : Geometry.b3545.half 2 false=Geometry.b3861 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3861
  · have he : Geometry.b3545.half 2 true=Geometry.b3862 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3862

theorem bound3544 : BoxMajorant Geometry.b3544 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3544.Widths)
  · have he : Geometry.b3544.half 2 false=Geometry.b3859 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3859
  · have he : Geometry.b3544.half 2 true=Geometry.b3860 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3860

theorem bound3543 : BoxMajorant Geometry.b3543 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3543.Widths)
  · have he : Geometry.b3543.half 2 false=Geometry.b3857 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3857
  · have he : Geometry.b3543.half 2 true=Geometry.b3858 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3858

theorem bound3270 : BoxMajorant Geometry.b3270 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3270.Widths)
  · have he : Geometry.b3270.half 1 false=Geometry.b3545 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3545
  · have he : Geometry.b3270.half 1 true=Geometry.b3546 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3546

theorem bound3269 : BoxMajorant Geometry.b3269 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3269.Widths)
  · have he : Geometry.b3269.half 1 false=Geometry.b3543 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3543
  · have he : Geometry.b3269.half 1 true=Geometry.b3544 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3544

theorem bound2942 : BoxMajorant Geometry.b2942 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2942.Widths)
  · have he : Geometry.b2942.half 0 false=Geometry.b3269 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3269
  · have he : Geometry.b2942.half 0 true=Geometry.b3270 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3270

end N7.Kernel.Cover
