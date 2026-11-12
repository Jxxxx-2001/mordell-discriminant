import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.LocalBridge
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.Local.C2LargeMajorant
import N7.Kernel.PositiveGroups.G0116
import N7.Kernel.PositiveGroups.G0154
import N7.Kernel.PositiveGroups.G0191
import N7.Kernel.PositiveGroups.G0192
import N7.Kernel.PositiveGroups.G0232
import N7.Kernel.PositiveGroups.G0271
import N7.Kernel.PositiveGroups.G0272
import N7.Kernel.PositiveGroups.G0298
import N7.Kernel.PositiveGroups.G0299
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5042 : BoxMajorant Geometry.b5042 := by
  exact PositiveLeaves.L1215.bound

theorem bound5041 : BoxMajorant Geometry.b5041 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5041 Local.C2.center Local.C2.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C2.large_near_majorant hn

theorem bound5040 : BoxMajorant Geometry.b5040 := by
  exact PositiveLeaves.L1217.bound

theorem bound5039 : BoxMajorant Geometry.b5039 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5039 Local.C2.center Local.C2.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C2.large_near_majorant hn

theorem bound5038 : BoxMajorant Geometry.b5038 := by
  exact PositiveLeaves.L1219.bound

theorem bound5037 : BoxMajorant Geometry.b5037 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5037 Local.C2.center Local.C2.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C2.large_near_majorant hn

theorem bound4672 : BoxMajorant Geometry.b4672 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4672.Widths)
  · have he : Geometry.b4672.half 2 false=Geometry.b5041 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5041
  · have he : Geometry.b4672.half 2 true=Geometry.b5042 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5042

theorem bound4671 : BoxMajorant Geometry.b4671 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4671.Widths)
  · have he : Geometry.b4671.half 2 false=Geometry.b5039 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5039
  · have he : Geometry.b4671.half 2 true=Geometry.b5040 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5040

theorem bound4670 : BoxMajorant Geometry.b4670 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4670.Widths)
  · have he : Geometry.b4670.half 2 false=Geometry.b5037 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5037
  · have he : Geometry.b4670.half 2 true=Geometry.b5038 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5038

theorem bound4669 : BoxMajorant Geometry.b4669 := by
  exact PositiveLeaves.L1221.bound

theorem bound4668 : BoxMajorant Geometry.b4668 := by
  exact PositiveLeaves.L1224.bound

theorem bound4667 : BoxMajorant Geometry.b4667 := by
  exact PositiveLeaves.L1225.bound

theorem bound4666 : BoxMajorant Geometry.b4666 := by
  exact PositiveLeaves.L1226.bound

theorem bound4665 : BoxMajorant Geometry.b4665 := by
  exact PositiveLeaves.L1227.bound

theorem bound4406 : BoxMajorant Geometry.b4406 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4406.Widths)
  · have he : Geometry.b4406.half 1 false=Geometry.b4671 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4671
  · have he : Geometry.b4406.half 1 true=Geometry.b4672 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4672

theorem bound4405 : BoxMajorant Geometry.b4405 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4405.Widths)
  · have he : Geometry.b4405.half 1 false=Geometry.b4669 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4669
  · have he : Geometry.b4405.half 1 true=Geometry.b4670 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4670

theorem bound4404 : BoxMajorant Geometry.b4404 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4404.Widths)
  · have he : Geometry.b4404.half 1 false=Geometry.b4667 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4667
  · have he : Geometry.b4404.half 1 true=Geometry.b4668 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4668

theorem bound4403 : BoxMajorant Geometry.b4403 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4403.Widths)
  · have he : Geometry.b4403.half 1 false=Geometry.b4665 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4665
  · have he : Geometry.b4403.half 1 true=Geometry.b4666 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4666

theorem bound4064 : BoxMajorant Geometry.b4064 := by
  exact PositiveLeaves.L1214.bound

theorem bound4063 : BoxMajorant Geometry.b4063 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4063.Widths)
  · have he : Geometry.b4063.half 0 false=Geometry.b4405 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4405
  · have he : Geometry.b4063.half 0 true=Geometry.b4406 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4406

theorem bound4062 : BoxMajorant Geometry.b4062 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4062.Widths)
  · have he : Geometry.b4062.half 0 false=Geometry.b4403 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4403
  · have he : Geometry.b4062.half 0 true=Geometry.b4404 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4404

theorem bound4061 : BoxMajorant Geometry.b4061 := by
  exact PositiveLeaves.L1228.bound

theorem bound3666 : BoxMajorant Geometry.b3666 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3666.Widths)
  · have he : Geometry.b3666.half 2 false=Geometry.b4063 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4063
  · have he : Geometry.b3666.half 2 true=Geometry.b4064 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4064

theorem bound3665 : BoxMajorant Geometry.b3665 := by
  exact PositiveLeaves.L1222.bound

theorem bound3664 : BoxMajorant Geometry.b3664 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3664.Widths)
  · have he : Geometry.b3664.half 2 false=Geometry.b4061 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4061
  · have he : Geometry.b3664.half 2 true=Geometry.b4062 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4062

theorem bound3663 : BoxMajorant Geometry.b3663 := by
  exact PositiveLeaves.L1229.bound

theorem bound3400 : BoxMajorant Geometry.b3400 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3400.Widths)
  · have he : Geometry.b3400.half 1 false=Geometry.b3665 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3665
  · have he : Geometry.b3400.half 1 true=Geometry.b3666 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3666

theorem bound3399 : BoxMajorant Geometry.b3399 := by
  exact PositiveLeaves.L1223.bound

theorem bound3398 : BoxMajorant Geometry.b3398 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3398.Widths)
  · have he : Geometry.b3398.half 1 false=Geometry.b3663 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3663
  · have he : Geometry.b3398.half 1 true=Geometry.b3664 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3664

theorem bound3397 : BoxMajorant Geometry.b3397 := by
  exact PositiveLeaves.L1230.bound

theorem bound3066 : BoxMajorant Geometry.b3066 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3066.Widths)
  · have he : Geometry.b3066.half 0 false=Geometry.b3399 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3399
  · have he : Geometry.b3066.half 0 true=Geometry.b3400 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3400

theorem bound3065 : BoxMajorant Geometry.b3065 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3065.Widths)
  · have he : Geometry.b3065.half 0 false=Geometry.b3397 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3397
  · have he : Geometry.b3065.half 0 true=Geometry.b3398 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3398

theorem bound2662 : BoxMajorant Geometry.b2662 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2662.Widths)
  · have he : Geometry.b2662.half 2 false=Geometry.b3065 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3065
  · have he : Geometry.b2662.half 2 true=Geometry.b3066 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3066

theorem bound2661 : BoxMajorant Geometry.b2661 := by
  exact PositiveLeaves.L1231.bound

theorem bound2290 : BoxMajorant Geometry.b2290 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2290.Widths)
  · have he : Geometry.b2290.half 1 false=Geometry.b2661 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2661
  · have he : Geometry.b2290.half 1 true=Geometry.b2662 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2662

theorem bound2289 : BoxMajorant Geometry.b2289 := by
  exact PositiveLeaves.L1232.bound

theorem bound1668 : BoxMajorant Geometry.b1668 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1668.Widths)
  · have he : Geometry.b1668.half 0 false=Geometry.b2289 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2289
  · have he : Geometry.b1668.half 0 true=Geometry.b2290 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2290

end N7.Kernel.Cover
