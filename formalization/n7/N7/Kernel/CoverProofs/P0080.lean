import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverGeometry.G0047
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverProofs.P0287
import N7.Kernel.CoverProofs.P0288
import N7.Kernel.CoverProofs.P0289
import N7.Kernel.CoverProofs.P0290
import N7.Kernel.PositiveGroups.G0155
import N7.Kernel.PositiveGroups.G0192
import N7.Kernel.PositiveGroups.G0193
import N7.Kernel.PositiveGroups.G0232
import N7.Kernel.PositiveGroups.G0272
import N7.Kernel.PositiveGroups.G0299
import N7.Kernel.PositiveGroups.G0324
import N7.Kernel.PositiveGroups.G0354
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5359 : BoxMajorant Geometry.b5359 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5359 0 (by decide +kernel) x hx hd ho).elim

theorem bound5358 : BoxMajorant Geometry.b5358 := by
  exact PositiveLeaves.L1306.bound

theorem bound5355 : BoxMajorant Geometry.b5355 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5355 2 (by decide +kernel) x hx hd ho).elim

theorem bound5254 : BoxMajorant Geometry.b5254 := by
  exact PositiveLeaves.L1263.bound

theorem bound5252 : BoxMajorant Geometry.b5252 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5252 0 (by decide +kernel) x hx hd ho).elim

theorem bound5251 : BoxMajorant Geometry.b5251 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5251.Widths)
  · have he : Geometry.b5251.half 1 false=Geometry.b5359 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5359
  · have he : Geometry.b5251.half 1 true=Geometry.b5360 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5360

theorem bound5250 : BoxMajorant Geometry.b5250 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5250.Widths)
  · have he : Geometry.b5250.half 1 false=Geometry.b5357 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5357
  · have he : Geometry.b5250.half 1 true=Geometry.b5358 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5358

theorem bound5249 : BoxMajorant Geometry.b5249 := by
  exact PositiveLeaves.L1311.bound

theorem bound5248 : BoxMajorant Geometry.b5248 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5248.Widths)
  · have he : Geometry.b5248.half 1 false=Geometry.b5355 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5355
  · have he : Geometry.b5248.half 1 true=Geometry.b5356 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5356

theorem bound5247 : BoxMajorant Geometry.b5247 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5247 2 (by decide +kernel) x hx hd ho).elim

theorem bound5036 : BoxMajorant Geometry.b5036 := by
  exact PositiveLeaves.L1262.bound

theorem bound5035 : BoxMajorant Geometry.b5035 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5035.Widths)
  · have he : Geometry.b5035.half 0 false=Geometry.b5253 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5253
  · have he : Geometry.b5035.half 0 true=Geometry.b5254 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5254

theorem bound5034 : BoxMajorant Geometry.b5034 := by
  exact PositiveLeaves.L1299.bound

theorem bound5033 : BoxMajorant Geometry.b5033 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5033.Widths)
  · have he : Geometry.b5033.half 0 false=Geometry.b5251 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5251
  · have he : Geometry.b5033.half 0 true=Geometry.b5252 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5252

theorem bound5032 : BoxMajorant Geometry.b5032 := by
  exact PositiveLeaves.L1305.bound

theorem bound5031 : BoxMajorant Geometry.b5031 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5031.Widths)
  · have he : Geometry.b5031.half 0 false=Geometry.b5249 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5249
  · have he : Geometry.b5031.half 0 true=Geometry.b5250 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5250

theorem bound5030 : BoxMajorant Geometry.b5030 := by
  exact PositiveLeaves.L1312.bound

theorem bound5029 : BoxMajorant Geometry.b5029 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5029.Widths)
  · have he : Geometry.b5029.half 0 false=Geometry.b5247 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5247
  · have he : Geometry.b5029.half 0 true=Geometry.b5248 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5248

theorem bound4664 : BoxMajorant Geometry.b4664 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4664.Widths)
  · have he : Geometry.b4664.half 2 false=Geometry.b5035 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5035
  · have he : Geometry.b4664.half 2 true=Geometry.b5036 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5036

theorem bound4663 : BoxMajorant Geometry.b4663 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4663.Widths)
  · have he : Geometry.b4663.half 2 false=Geometry.b5033 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5033
  · have he : Geometry.b4663.half 2 true=Geometry.b5034 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5034

theorem bound4662 : BoxMajorant Geometry.b4662 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4662.Widths)
  · have he : Geometry.b4662.half 2 false=Geometry.b5031 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5031
  · have he : Geometry.b4662.half 2 true=Geometry.b5032 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5032

theorem bound4661 : BoxMajorant Geometry.b4661 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4661.Widths)
  · have he : Geometry.b4661.half 2 false=Geometry.b5029 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5029
  · have he : Geometry.b4661.half 2 true=Geometry.b5030 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5030

theorem bound4402 : BoxMajorant Geometry.b4402 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4402.Widths)
  · have he : Geometry.b4402.half 1 false=Geometry.b4663 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4663
  · have he : Geometry.b4402.half 1 true=Geometry.b4664 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4664

theorem bound4401 : BoxMajorant Geometry.b4401 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4401.Widths)
  · have he : Geometry.b4401.half 1 false=Geometry.b4661 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4661
  · have he : Geometry.b4401.half 1 true=Geometry.b4662 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4662

theorem bound4060 : BoxMajorant Geometry.b4060 := by
  exact PositiveLeaves.L1261.bound

theorem bound4059 : BoxMajorant Geometry.b4059 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4059.Widths)
  · have he : Geometry.b4059.half 0 false=Geometry.b4401 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4401
  · have he : Geometry.b4059.half 0 true=Geometry.b4402 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4402

theorem bound3662 : BoxMajorant Geometry.b3662 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3662.Widths)
  · have he : Geometry.b3662.half 2 false=Geometry.b4059 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4059
  · have he : Geometry.b3662.half 2 true=Geometry.b4060 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4060

theorem bound3661 : BoxMajorant Geometry.b3661 := by
  exact PositiveLeaves.L1317.bound

theorem bound3396 : BoxMajorant Geometry.b3396 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3396.Widths)
  · have he : Geometry.b3396.half 1 false=Geometry.b3661 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3661
  · have he : Geometry.b3396.half 1 true=Geometry.b3662 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3662

theorem bound3395 : BoxMajorant Geometry.b3395 := by
  exact PositiveLeaves.L1318.bound

theorem bound3060 : BoxMajorant Geometry.b3060 := by
  exact PositiveLeaves.L1260.bound

theorem bound3059 : BoxMajorant Geometry.b3059 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3059.Widths)
  · have he : Geometry.b3059.half 0 false=Geometry.b3395 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3395
  · have he : Geometry.b3059.half 0 true=Geometry.b3396 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3396

theorem bound2652 : BoxMajorant Geometry.b2652 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2652.Widths)
  · have he : Geometry.b2652.half 2 false=Geometry.b3059 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3059
  · have he : Geometry.b2652.half 2 true=Geometry.b3060 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3060

theorem bound2651 : BoxMajorant Geometry.b2651 := by
  exact PositiveLeaves.L1319.bound

theorem bound2280 : BoxMajorant Geometry.b2280 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2280.Widths)
  · have he : Geometry.b2280.half 1 false=Geometry.b2651 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2651
  · have he : Geometry.b2280.half 1 true=Geometry.b2652 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2652

end N7.Kernel.Cover
