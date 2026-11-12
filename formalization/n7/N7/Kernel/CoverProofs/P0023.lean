import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0004
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.PositiveGroups.G0009
import N7.Kernel.PositiveGroups.G0016
import N7.Kernel.PositiveGroups.G0017
import N7.Kernel.PositiveGroups.G0034
import N7.Kernel.PositiveGroups.G0035
import N7.Kernel.PositiveGroups.G0036
import N7.Kernel.PositiveGroups.G0037
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound722 : BoxMajorant Geometry.b722 := by
  exact PositiveLeaves.L73.bound

theorem bound721 : BoxMajorant Geometry.b721 := by
  exact PositiveLeaves.L74.bound

theorem bound720 : BoxMajorant Geometry.b720 := by
  exact PositiveLeaves.L75.bound

theorem bound719 : BoxMajorant Geometry.b719 := by
  exact PositiveLeaves.L76.bound

theorem bound718 : BoxMajorant Geometry.b718 := by
  exact PositiveLeaves.L77.bound

theorem bound717 : BoxMajorant Geometry.b717 := by
  exact PositiveLeaves.L78.bound

theorem bound716 : BoxMajorant Geometry.b716 := by
  exact PositiveLeaves.L79.bound

theorem bound715 : BoxMajorant Geometry.b715 := by
  exact PositiveLeaves.L80.bound

theorem bound714 : BoxMajorant Geometry.b714 := by
  exact PositiveLeaves.L81.bound

theorem bound713 : BoxMajorant Geometry.b713 := by
  exact PositiveLeaves.L82.bound

theorem bound712 : BoxMajorant Geometry.b712 := by
  exact PositiveLeaves.L84.bound

theorem bound711 : BoxMajorant Geometry.b711 := by
  exact PositiveLeaves.L85.bound

theorem bound710 : BoxMajorant Geometry.b710 := by
  exact PositiveLeaves.L88.bound

theorem bound709 : BoxMajorant Geometry.b709 := by
  exact PositiveLeaves.L89.bound

theorem bound462 : BoxMajorant Geometry.b462 := by
  exact PositiveLeaves.L72.bound

theorem bound461 : BoxMajorant Geometry.b461 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b461.Widths)
  · have he : Geometry.b461.half 2 false=Geometry.b721 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound721
  · have he : Geometry.b461.half 2 true=Geometry.b722 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound722

theorem bound460 : BoxMajorant Geometry.b460 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b460.Widths)
  · have he : Geometry.b460.half 2 false=Geometry.b719 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound719
  · have he : Geometry.b460.half 2 true=Geometry.b720 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound720

theorem bound459 : BoxMajorant Geometry.b459 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b459.Widths)
  · have he : Geometry.b459.half 2 false=Geometry.b717 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound717
  · have he : Geometry.b459.half 2 true=Geometry.b718 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound718

theorem bound458 : BoxMajorant Geometry.b458 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b458.Widths)
  · have he : Geometry.b458.half 2 false=Geometry.b715 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound715
  · have he : Geometry.b458.half 2 true=Geometry.b716 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound716

theorem bound457 : BoxMajorant Geometry.b457 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b457.Widths)
  · have he : Geometry.b457.half 2 false=Geometry.b713 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound713
  · have he : Geometry.b457.half 2 true=Geometry.b714 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound714

theorem bound456 : BoxMajorant Geometry.b456 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b456.Widths)
  · have he : Geometry.b456.half 2 false=Geometry.b711 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound711
  · have he : Geometry.b456.half 2 true=Geometry.b712 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound712

theorem bound455 : BoxMajorant Geometry.b455 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b455 0 (by decide +kernel) x hx hd ho).elim

theorem bound454 : BoxMajorant Geometry.b454 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b454.Widths)
  · have he : Geometry.b454.half 2 false=Geometry.b709 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound709
  · have he : Geometry.b454.half 2 true=Geometry.b710 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound710

theorem bound453 : BoxMajorant Geometry.b453 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b453 0 (by decide +kernel) x hx hd ho).elim

theorem bound294 : BoxMajorant Geometry.b294 := by
  exact PositiveLeaves.L71.bound

theorem bound293 : BoxMajorant Geometry.b293 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b293.Widths)
  · have he : Geometry.b293.half 1 false=Geometry.b461 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound461
  · have he : Geometry.b293.half 1 true=Geometry.b462 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound462

theorem bound292 : BoxMajorant Geometry.b292 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b292.Widths)
  · have he : Geometry.b292.half 1 false=Geometry.b459 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound459
  · have he : Geometry.b292.half 1 true=Geometry.b460 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound460

theorem bound291 : BoxMajorant Geometry.b291 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b291.Widths)
  · have he : Geometry.b291.half 1 false=Geometry.b457 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound457
  · have he : Geometry.b291.half 1 true=Geometry.b458 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound458

theorem bound290 : BoxMajorant Geometry.b290 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b290 0 (by decide +kernel) x hx hd ho).elim

theorem bound289 : BoxMajorant Geometry.b289 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b289.Widths)
  · have he : Geometry.b289.half 1 false=Geometry.b455 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound455
  · have he : Geometry.b289.half 1 true=Geometry.b456 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound456

theorem bound288 : BoxMajorant Geometry.b288 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b288 0 (by decide +kernel) x hx hd ho).elim

theorem bound287 : BoxMajorant Geometry.b287 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b287.Widths)
  · have he : Geometry.b287.half 1 false=Geometry.b453 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound453
  · have he : Geometry.b287.half 1 true=Geometry.b454 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound454

theorem bound182 : BoxMajorant Geometry.b182 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b182.Widths)
  · have he : Geometry.b182.half 0 false=Geometry.b293 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound293
  · have he : Geometry.b182.half 0 true=Geometry.b294 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound294

theorem bound181 : BoxMajorant Geometry.b181 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b181.Widths)
  · have he : Geometry.b181.half 0 false=Geometry.b291 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound291
  · have he : Geometry.b181.half 0 true=Geometry.b292 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound292

theorem bound180 : BoxMajorant Geometry.b180 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b180.Widths)
  · have he : Geometry.b180.half 0 false=Geometry.b289 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound289
  · have he : Geometry.b180.half 0 true=Geometry.b290 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound290

theorem bound179 : BoxMajorant Geometry.b179 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b179.Widths)
  · have he : Geometry.b179.half 0 false=Geometry.b287 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound287
  · have he : Geometry.b179.half 0 true=Geometry.b288 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound288

theorem bound106 : BoxMajorant Geometry.b106 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b106.Widths)
  · have he : Geometry.b106.half 2 false=Geometry.b181 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound181
  · have he : Geometry.b106.half 2 true=Geometry.b182 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound182

theorem bound105 : BoxMajorant Geometry.b105 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b105.Widths)
  · have he : Geometry.b105.half 2 false=Geometry.b179 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound179
  · have he : Geometry.b105.half 2 true=Geometry.b180 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound180

theorem bound58 : BoxMajorant Geometry.b58 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b58.Widths)
  · have he : Geometry.b58.half 1 false=Geometry.b105 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound105
  · have he : Geometry.b58.half 1 true=Geometry.b106 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound106

end N7.Kernel.Cover
