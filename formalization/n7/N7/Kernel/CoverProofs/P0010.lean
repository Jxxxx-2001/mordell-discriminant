import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0026
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.CoverProofs.P0080
import N7.Kernel.CoverProofs.P0081
import N7.Kernel.CoverProofs.P0082
import N7.Kernel.CoverProofs.P0083
import N7.Kernel.CoverProofs.P0084
import N7.Kernel.CoverProofs.P0085
import N7.Kernel.PositiveGroups.FourPilot
import N7.Kernel.PositiveGroups.G0006
import N7.Kernel.PositiveGroups.G0049
import N7.Kernel.PositiveGroups.G0117
import N7.Kernel.PositiveGroups.G0154
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2649 : BoxMajorant Geometry.b2649 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2649 2 (by decide +kernel) x hx hd ho).elim

theorem bound2288 : BoxMajorant Geometry.b2288 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2288 0 (by decide +kernel) x hx hd ho).elim

theorem bound2286 : BoxMajorant Geometry.b2286 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2286 0 (by decide +kernel) x hx hd ho).elim

theorem bound2284 : BoxMajorant Geometry.b2284 := by
  exact PositiveLeaves.L1253.bound

theorem bound2283 : BoxMajorant Geometry.b2283 := by
  exact PositiveLeaves.L1254.bound

theorem bound2279 : BoxMajorant Geometry.b2279 := by
  exact PositiveLeaves.L1320.bound

theorem bound2278 : BoxMajorant Geometry.b2278 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2278.Widths)
  · have he : Geometry.b2278.half 1 false=Geometry.b2649 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2649
  · have he : Geometry.b2278.half 1 true=Geometry.b2650 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2650

theorem bound2277 : BoxMajorant Geometry.b2277 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2277 2 (by decide +kernel) x hx hd ho).elim

theorem bound1666 : BoxMajorant Geometry.b1666 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1666.Widths)
  · have he : Geometry.b1666.half 0 false=Geometry.b2287 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2287
  · have he : Geometry.b1666.half 0 true=Geometry.b2288 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2288

theorem bound1665 : BoxMajorant Geometry.b1665 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1665.Widths)
  · have he : Geometry.b1665.half 0 false=Geometry.b2285 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2285
  · have he : Geometry.b1665.half 0 true=Geometry.b2286 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2286

theorem bound1664 : BoxMajorant Geometry.b1664 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1664.Widths)
  · have he : Geometry.b1664.half 0 false=Geometry.b2283 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2283
  · have he : Geometry.b1664.half 0 true=Geometry.b2284 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2284

theorem bound1663 : BoxMajorant Geometry.b1663 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1663.Widths)
  · have he : Geometry.b1663.half 0 false=Geometry.b2281 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2281
  · have he : Geometry.b1663.half 0 true=Geometry.b2282 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2282

theorem bound1662 : BoxMajorant Geometry.b1662 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1662.Widths)
  · have he : Geometry.b1662.half 0 false=Geometry.b2279 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2279
  · have he : Geometry.b1662.half 0 true=Geometry.b2280 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2280

theorem bound1661 : BoxMajorant Geometry.b1661 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1661.Widths)
  · have he : Geometry.b1661.half 0 false=Geometry.b2277 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2277
  · have he : Geometry.b1661.half 0 true=Geometry.b2278 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2278

theorem bound1174 : BoxMajorant Geometry.b1174 := by
  exact PositiveLeaves.L1245.bound

theorem bound1173 : BoxMajorant Geometry.b1173 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1173.Widths)
  · have he : Geometry.b1173.half 2 false=Geometry.b1665 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1665
  · have he : Geometry.b1173.half 2 true=Geometry.b1666 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1666

theorem bound1172 : BoxMajorant Geometry.b1172 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1172.Widths)
  · have he : Geometry.b1172.half 2 false=Geometry.b1663 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1663
  · have he : Geometry.b1172.half 2 true=Geometry.b1664 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1664

theorem bound1171 : BoxMajorant Geometry.b1171 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1171.Widths)
  · have he : Geometry.b1171.half 2 false=Geometry.b1661 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1661
  · have he : Geometry.b1171.half 2 true=Geometry.b1662 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1662

theorem bound1170 : BoxMajorant Geometry.b1170 := by
  exact PositiveLeaves.L1330.bound

theorem bound1169 : BoxMajorant Geometry.b1169 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1169 2 (by decide +kernel) x hx hd ho).elim

theorem bound856 : BoxMajorant Geometry.b856 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b856.Widths)
  · have he : Geometry.b856.half 1 false=Geometry.b1173 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1173
  · have he : Geometry.b856.half 1 true=Geometry.b1174 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1174

theorem bound855 : BoxMajorant Geometry.b855 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b855.Widths)
  · have he : Geometry.b855.half 1 false=Geometry.b1171 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1171
  · have he : Geometry.b855.half 1 true=Geometry.b1172 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1172

theorem bound854 : BoxMajorant Geometry.b854 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b854.Widths)
  · have he : Geometry.b854.half 1 false=Geometry.b1169 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1169
  · have he : Geometry.b854.half 1 true=Geometry.b1170 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1170

theorem bound853 : BoxMajorant Geometry.b853 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b853 2 (by decide +kernel) x hx hd ho).elim

theorem bound582 : BoxMajorant Geometry.b582 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b582.Widths)
  · have he : Geometry.b582.half 0 false=Geometry.b855 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound855
  · have he : Geometry.b582.half 0 true=Geometry.b856 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound856

theorem bound581 : BoxMajorant Geometry.b581 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b581.Widths)
  · have he : Geometry.b581.half 0 false=Geometry.b853 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound853
  · have he : Geometry.b581.half 0 true=Geometry.b854 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound854

theorem bound374 : BoxMajorant Geometry.b374 := by
  exact PositiveLeaves.L1244.bound

theorem bound373 : BoxMajorant Geometry.b373 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b373.Widths)
  · have he : Geometry.b373.half 2 false=Geometry.b581 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound581
  · have he : Geometry.b373.half 2 true=Geometry.b582 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound582

theorem bound240 : BoxMajorant Geometry.b240 := by
  exact PositiveLeaves.L1243.bound

theorem bound239 : BoxMajorant Geometry.b239 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b239.Widths)
  · have he : Geometry.b239.half 1 false=Geometry.b373 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound373
  · have he : Geometry.b239.half 1 true=Geometry.b374 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound374

theorem bound238 : BoxMajorant Geometry.b238 := by
  exact PositiveLeaves.L1333.bound

theorem bound237 : BoxMajorant Geometry.b237 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b237 2 (by decide +kernel) x hx hd ho).elim

theorem bound140 : BoxMajorant Geometry.b140 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b140.Widths)
  · have he : Geometry.b140.half 0 false=Geometry.b239 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound239
  · have he : Geometry.b140.half 0 true=Geometry.b240 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound240

theorem bound139 : BoxMajorant Geometry.b139 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b139.Widths)
  · have he : Geometry.b139.half 0 false=Geometry.b237 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound237
  · have he : Geometry.b139.half 0 true=Geometry.b238 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound238

theorem bound80 : BoxMajorant Geometry.b80 := by
  exact PositiveLeaves.L1242.bound

theorem bound79 : BoxMajorant Geometry.b79 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b79.Widths)
  · have he : Geometry.b79.half 2 false=Geometry.b139 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound139
  · have he : Geometry.b79.half 2 true=Geometry.b140 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound140

theorem bound43 : BoxMajorant Geometry.b43 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b43.Widths)
  · have he : Geometry.b43.half 1 false=Geometry.b79 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound79
  · have he : Geometry.b43.half 1 true=Geometry.b80 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound80

end N7.Kernel.Cover
