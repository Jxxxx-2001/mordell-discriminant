import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0365
import N7.Kernel.PositiveGroups.G0413
import N7.Kernel.PositiveGroups.G0433
import N7.Kernel.PositiveGroups.G0434
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5240 : BoxMajorant Geometry.b5240 := by
  exact PositiveLeaves.L1480.bound

theorem bound5239 : BoxMajorant Geometry.b5239 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5239 2 (by decide +kernel) x hx hd ho).elim

theorem bound5238 : BoxMajorant Geometry.b5238 := by
  exact PositiveLeaves.L1486.bound

theorem bound5237 : BoxMajorant Geometry.b5237 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5237 2 (by decide +kernel) x hx hd ho).elim

theorem bound5020 : BoxMajorant Geometry.b5020 := by
  exact PositiveLeaves.L1479.bound

theorem bound5019 : BoxMajorant Geometry.b5019 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5019.Widths)
  · have he : Geometry.b5019.half 0 false=Geometry.b5239 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5239
  · have he : Geometry.b5019.half 0 true=Geometry.b5240 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5240

theorem bound5018 : BoxMajorant Geometry.b5018 := by
  exact PositiveLeaves.L1482.bound

theorem bound5017 : BoxMajorant Geometry.b5017 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5017 2 (by decide +kernel) x hx hd ho).elim

theorem bound5016 : BoxMajorant Geometry.b5016 := by
  exact PositiveLeaves.L1484.bound

theorem bound5015 : BoxMajorant Geometry.b5015 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5015 2 (by decide +kernel) x hx hd ho).elim

theorem bound5014 : BoxMajorant Geometry.b5014 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5014.Widths)
  · have he : Geometry.b5014.half 0 false=Geometry.b5237 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5237
  · have he : Geometry.b5014.half 0 true=Geometry.b5238 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5238

theorem bound5013 : BoxMajorant Geometry.b5013 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5013 2 (by decide +kernel) x hx hd ho).elim

theorem bound4652 : BoxMajorant Geometry.b4652 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4652.Widths)
  · have he : Geometry.b4652.half 2 false=Geometry.b5019 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5019
  · have he : Geometry.b4652.half 2 true=Geometry.b5020 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5020

theorem bound4651 : BoxMajorant Geometry.b4651 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4651.Widths)
  · have he : Geometry.b4651.half 2 false=Geometry.b5017 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5017
  · have he : Geometry.b4651.half 2 true=Geometry.b5018 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5018

theorem bound4650 : BoxMajorant Geometry.b4650 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4650.Widths)
  · have he : Geometry.b4650.half 2 false=Geometry.b5015 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5015
  · have he : Geometry.b4650.half 2 true=Geometry.b5016 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5016

theorem bound4649 : BoxMajorant Geometry.b4649 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4649.Widths)
  · have he : Geometry.b4649.half 2 false=Geometry.b5013 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5013
  · have he : Geometry.b4649.half 2 true=Geometry.b5014 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5014

theorem bound4390 : BoxMajorant Geometry.b4390 := by
  exact PositiveLeaves.L1478.bound

theorem bound4389 : BoxMajorant Geometry.b4389 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4389.Widths)
  · have he : Geometry.b4389.half 1 false=Geometry.b4651 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4651
  · have he : Geometry.b4389.half 1 true=Geometry.b4652 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4652

theorem bound4388 : BoxMajorant Geometry.b4388 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4388.Widths)
  · have he : Geometry.b4388.half 1 false=Geometry.b4649 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4649
  · have he : Geometry.b4388.half 1 true=Geometry.b4650 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4650

theorem bound4387 : BoxMajorant Geometry.b4387 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4387 2 (by decide +kernel) x hx hd ho).elim

theorem bound4040 : BoxMajorant Geometry.b4040 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4040.Widths)
  · have he : Geometry.b4040.half 0 false=Geometry.b4389 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4389
  · have he : Geometry.b4040.half 0 true=Geometry.b4390 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4390

theorem bound4039 : BoxMajorant Geometry.b4039 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4039.Widths)
  · have he : Geometry.b4039.half 0 false=Geometry.b4387 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4387
  · have he : Geometry.b4039.half 0 true=Geometry.b4388 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4388

theorem bound3650 : BoxMajorant Geometry.b3650 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3650.Widths)
  · have he : Geometry.b3650.half 2 false=Geometry.b4039 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4039
  · have he : Geometry.b3650.half 2 true=Geometry.b4040 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4040

end N7.Kernel.Cover
