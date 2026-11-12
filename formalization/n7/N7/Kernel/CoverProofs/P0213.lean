import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverProofs.P0360
import N7.Kernel.CoverProofs.P0361
import N7.Kernel.PositiveGroups.G0266
import N7.Kernel.PositiveGroups.G0295
import N7.Kernel.PositiveGroups.G0319
import N7.Kernel.PositiveGroups.G0350
import N7.Kernel.PositiveGroups.G0351
import N7.Kernel.PositiveGroups.G0382
import N7.Kernel.PositiveGroups.G0405
import N7.Kernel.PositiveGroups.G0406
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5625 : BoxMajorant Geometry.b5625 := by
  exact PositiveLeaves.L2204.bound

theorem bound5624 : BoxMajorant Geometry.b5624 := by
  exact PositiveLeaves.L2205.bound

theorem bound5623 : BoxMajorant Geometry.b5623 := by
  exact PositiveLeaves.L2206.bound

theorem bound5592 : BoxMajorant Geometry.b5592 := by
  exact PositiveLeaves.L2186.bound

theorem bound5590 : BoxMajorant Geometry.b5590 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5590.Widths)
  · have he : Geometry.b5590.half 2 false=Geometry.b5625 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5625
  · have he : Geometry.b5590.half 2 true=Geometry.b5626 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5626

theorem bound5589 : BoxMajorant Geometry.b5589 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5589.Widths)
  · have he : Geometry.b5589.half 2 false=Geometry.b5623 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5623
  · have he : Geometry.b5589.half 2 true=Geometry.b5624 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5624

theorem bound5560 : BoxMajorant Geometry.b5560 := by
  exact PositiveLeaves.L2185.bound

theorem bound5559 : BoxMajorant Geometry.b5559 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5559.Widths)
  · have he : Geometry.b5559.half 1 false=Geometry.b5591 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5591
  · have he : Geometry.b5559.half 1 true=Geometry.b5592 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5592

theorem bound5558 : BoxMajorant Geometry.b5558 := by
  exact PositiveLeaves.L2195.bound

theorem bound5557 : BoxMajorant Geometry.b5557 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5557.Widths)
  · have he : Geometry.b5557.half 1 false=Geometry.b5589 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5589
  · have he : Geometry.b5557.half 1 true=Geometry.b5590 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5590

theorem bound5476 : BoxMajorant Geometry.b5476 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5476.Widths)
  · have he : Geometry.b5476.half 0 false=Geometry.b5559 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5559
  · have he : Geometry.b5476.half 0 true=Geometry.b5560 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5560

theorem bound5475 : BoxMajorant Geometry.b5475 := by
  exact PositiveLeaves.L2192.bound

theorem bound5474 : BoxMajorant Geometry.b5474 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5474.Widths)
  · have he : Geometry.b5474.half 0 false=Geometry.b5557 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5557
  · have he : Geometry.b5474.half 0 true=Geometry.b5558 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5558

theorem bound5473 : BoxMajorant Geometry.b5473 := by
  exact PositiveLeaves.L2207.bound

theorem bound5472 : BoxMajorant Geometry.b5472 := by
  exact PositiveLeaves.L2208.bound

theorem bound5471 : BoxMajorant Geometry.b5471 := by
  exact PositiveLeaves.L2209.bound

theorem bound5344 : BoxMajorant Geometry.b5344 := by
  exact PositiveLeaves.L2184.bound

theorem bound5343 : BoxMajorant Geometry.b5343 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5343.Widths)
  · have he : Geometry.b5343.half 2 false=Geometry.b5475 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5475
  · have he : Geometry.b5343.half 2 true=Geometry.b5476 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5476

theorem bound5342 : BoxMajorant Geometry.b5342 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5342.Widths)
  · have he : Geometry.b5342.half 2 false=Geometry.b5473 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5473
  · have he : Geometry.b5342.half 2 true=Geometry.b5474 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5474

theorem bound5341 : BoxMajorant Geometry.b5341 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5341.Widths)
  · have he : Geometry.b5341.half 2 false=Geometry.b5471 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5471
  · have he : Geometry.b5341.half 2 true=Geometry.b5472 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5472

theorem bound5160 : BoxMajorant Geometry.b5160 := by
  exact PositiveLeaves.L2183.bound

theorem bound5159 : BoxMajorant Geometry.b5159 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5159.Widths)
  · have he : Geometry.b5159.half 1 false=Geometry.b5343 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5343
  · have he : Geometry.b5159.half 1 true=Geometry.b5344 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5344

theorem bound5158 : BoxMajorant Geometry.b5158 := by
  exact PositiveLeaves.L2194.bound

theorem bound5157 : BoxMajorant Geometry.b5157 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5157.Widths)
  · have he : Geometry.b5157.half 1 false=Geometry.b5341 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5341
  · have he : Geometry.b5157.half 1 true=Geometry.b5342 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5342

theorem bound4810 : BoxMajorant Geometry.b4810 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4810.Widths)
  · have he : Geometry.b4810.half 0 false=Geometry.b5159 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5159
  · have he : Geometry.b4810.half 0 true=Geometry.b5160 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5160

theorem bound4809 : BoxMajorant Geometry.b4809 := by
  exact PositiveLeaves.L2193.bound

theorem bound4808 : BoxMajorant Geometry.b4808 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4808.Widths)
  · have he : Geometry.b4808.half 0 false=Geometry.b5157 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5157
  · have he : Geometry.b4808.half 0 true=Geometry.b5158 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5158

theorem bound4807 : BoxMajorant Geometry.b4807 := by
  exact PositiveLeaves.L2210.bound

theorem bound4514 : BoxMajorant Geometry.b4514 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4514.Widths)
  · have he : Geometry.b4514.half 2 false=Geometry.b4809 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4809
  · have he : Geometry.b4514.half 2 true=Geometry.b4810 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4810

theorem bound4513 : BoxMajorant Geometry.b4513 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4513.Widths)
  · have he : Geometry.b4513.half 2 false=Geometry.b4807 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4807
  · have he : Geometry.b4513.half 2 true=Geometry.b4808 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4808

theorem bound4210 : BoxMajorant Geometry.b4210 := by
  exact PositiveLeaves.L2182.bound

theorem bound4209 : BoxMajorant Geometry.b4209 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4209.Widths)
  · have he : Geometry.b4209.half 1 false=Geometry.b4513 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4513
  · have he : Geometry.b4209.half 1 true=Geometry.b4514 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4514

theorem bound3822 : BoxMajorant Geometry.b3822 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3822.Widths)
  · have he : Geometry.b3822.half 0 false=Geometry.b4209 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4209
  · have he : Geometry.b3822.half 0 true=Geometry.b4210 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4210

theorem bound3821 : BoxMajorant Geometry.b3821 := by
  exact PositiveLeaves.L2211.bound

theorem bound3520 : BoxMajorant Geometry.b3520 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3520.Widths)
  · have he : Geometry.b3520.half 2 false=Geometry.b3821 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3821
  · have he : Geometry.b3520.half 2 true=Geometry.b3822 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3822

end N7.Kernel.Cover
