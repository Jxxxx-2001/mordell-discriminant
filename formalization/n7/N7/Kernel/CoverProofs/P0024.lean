import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0004
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverProofs.P0173
import N7.Kernel.CoverProofs.P0174
import N7.Kernel.CoverProofs.P0175
import N7.Kernel.CoverProofs.P0176
import N7.Kernel.CoverProofs.P0177
import N7.Kernel.CoverProofs.P0178
import N7.Kernel.CoverProofs.P0179
import N7.Kernel.CoverProofs.P0180
import N7.Kernel.CoverProofs.P0181
import N7.Kernel.CoverProofs.P0182
import N7.Kernel.CoverProofs.P0183
import N7.Kernel.PositiveGroups.G0004
import N7.Kernel.PositiveGroups.G0017
import N7.Kernel.PositiveGroups.G0034
import N7.Kernel.PositiveGroups.G0035
import N7.Kernel.PositiveGroups.G0061
import N7.Kernel.PositiveGroups.G0062
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1014 : BoxMajorant Geometry.b1014 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1014 0 (by decide +kernel) x hx hd ho).elim

theorem bound736 : BoxMajorant Geometry.b736 := by
  exact PositiveLeaves.L23.bound

theorem bound735 : BoxMajorant Geometry.b735 := by
  exact PositiveLeaves.L24.bound

theorem bound734 : BoxMajorant Geometry.b734 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b734.Widths)
  · have he : Geometry.b734.half 0 false=Geometry.b1021 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1021
  · have he : Geometry.b734.half 0 true=Geometry.b1022 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1022

theorem bound733 : BoxMajorant Geometry.b733 := by
  exact PositiveLeaves.L31.bound

theorem bound732 : BoxMajorant Geometry.b732 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b732.Widths)
  · have he : Geometry.b732.half 0 false=Geometry.b1019 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1019
  · have he : Geometry.b732.half 0 true=Geometry.b1020 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1020

theorem bound731 : BoxMajorant Geometry.b731 := by
  exact PositiveLeaves.L39.bound

theorem bound730 : BoxMajorant Geometry.b730 := by
  exact PositiveLeaves.L40.bound

theorem bound729 : BoxMajorant Geometry.b729 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b729.Widths)
  · have he : Geometry.b729.half 0 false=Geometry.b1017 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1017
  · have he : Geometry.b729.half 0 true=Geometry.b1018 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1018

theorem bound728 : BoxMajorant Geometry.b728 := by
  exact PositiveLeaves.L49.bound

theorem bound727 : BoxMajorant Geometry.b727 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b727.Widths)
  · have he : Geometry.b727.half 0 false=Geometry.b1015 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1015
  · have he : Geometry.b727.half 0 true=Geometry.b1016 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1016

theorem bound726 : BoxMajorant Geometry.b726 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b726 1 (by decide +kernel) x hx hd ho).elim

theorem bound725 : BoxMajorant Geometry.b725 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b725.Widths)
  · have he : Geometry.b725.half 0 false=Geometry.b1013 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1013
  · have he : Geometry.b725.half 0 true=Geometry.b1014 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1014

theorem bound724 : BoxMajorant Geometry.b724 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b724 1 (by decide +kernel) x hx hd ho).elim

theorem bound723 : BoxMajorant Geometry.b723 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b723.Widths)
  · have he : Geometry.b723.half 0 false=Geometry.b1011 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1011
  · have he : Geometry.b723.half 0 true=Geometry.b1012 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1012

theorem bound470 : BoxMajorant Geometry.b470 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b470.Widths)
  · have he : Geometry.b470.half 2 false=Geometry.b735 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound735
  · have he : Geometry.b470.half 2 true=Geometry.b736 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound736

theorem bound469 : BoxMajorant Geometry.b469 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b469.Widths)
  · have he : Geometry.b469.half 2 false=Geometry.b733 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound733
  · have he : Geometry.b469.half 2 true=Geometry.b734 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound734

theorem bound468 : BoxMajorant Geometry.b468 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b468.Widths)
  · have he : Geometry.b468.half 2 false=Geometry.b731 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound731
  · have he : Geometry.b468.half 2 true=Geometry.b732 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound732

theorem bound467 : BoxMajorant Geometry.b467 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b467.Widths)
  · have he : Geometry.b467.half 2 false=Geometry.b729 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound729
  · have he : Geometry.b467.half 2 true=Geometry.b730 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound730

theorem bound466 : BoxMajorant Geometry.b466 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b466.Widths)
  · have he : Geometry.b466.half 2 false=Geometry.b727 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound727
  · have he : Geometry.b466.half 2 true=Geometry.b728 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound728

theorem bound465 : BoxMajorant Geometry.b465 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b465.Widths)
  · have he : Geometry.b465.half 2 false=Geometry.b725 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound725
  · have he : Geometry.b465.half 2 true=Geometry.b726 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound726

theorem bound464 : BoxMajorant Geometry.b464 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b464.Widths)
  · have he : Geometry.b464.half 2 false=Geometry.b723 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound723
  · have he : Geometry.b464.half 2 true=Geometry.b724 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound724

theorem bound463 : BoxMajorant Geometry.b463 := by
  exact PositiveLeaves.L70.bound

theorem bound298 : BoxMajorant Geometry.b298 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b298.Widths)
  · have he : Geometry.b298.half 1 false=Geometry.b469 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound469
  · have he : Geometry.b298.half 1 true=Geometry.b470 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound470

theorem bound297 : BoxMajorant Geometry.b297 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b297.Widths)
  · have he : Geometry.b297.half 1 false=Geometry.b467 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound467
  · have he : Geometry.b297.half 1 true=Geometry.b468 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound468

theorem bound296 : BoxMajorant Geometry.b296 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b296.Widths)
  · have he : Geometry.b296.half 1 false=Geometry.b465 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound465
  · have he : Geometry.b296.half 1 true=Geometry.b466 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound466

theorem bound295 : BoxMajorant Geometry.b295 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b295.Widths)
  · have he : Geometry.b295.half 1 false=Geometry.b463 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound463
  · have he : Geometry.b295.half 1 true=Geometry.b464 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound464

theorem bound186 : BoxMajorant Geometry.b186 := by
  exact PositiveLeaves.L22.bound

theorem bound185 : BoxMajorant Geometry.b185 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b185.Widths)
  · have he : Geometry.b185.half 0 false=Geometry.b297 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound297
  · have he : Geometry.b185.half 0 true=Geometry.b298 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound298

theorem bound184 : BoxMajorant Geometry.b184 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b184 1 (by decide +kernel) x hx hd ho).elim

theorem bound183 : BoxMajorant Geometry.b183 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b183.Widths)
  · have he : Geometry.b183.half 0 false=Geometry.b295 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound295
  · have he : Geometry.b183.half 0 true=Geometry.b296 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound296

theorem bound108 : BoxMajorant Geometry.b108 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b108.Widths)
  · have he : Geometry.b108.half 2 false=Geometry.b185 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound185
  · have he : Geometry.b108.half 2 true=Geometry.b186 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound186

theorem bound107 : BoxMajorant Geometry.b107 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b107.Widths)
  · have he : Geometry.b107.half 2 false=Geometry.b183 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound183
  · have he : Geometry.b107.half 2 true=Geometry.b184 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound184

theorem bound59 : BoxMajorant Geometry.b59 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b59.Widths)
  · have he : Geometry.b59.half 1 false=Geometry.b107 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound107
  · have he : Geometry.b59.half 1 true=Geometry.b108 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound108

end N7.Kernel.Cover
