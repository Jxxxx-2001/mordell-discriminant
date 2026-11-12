import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverProofs.P0298
import N7.Kernel.CoverProofs.P0299
import N7.Kernel.CoverProofs.P0300
import N7.Kernel.CoverProofs.P0301
import N7.Kernel.CoverProofs.P0302
import N7.Kernel.CoverProofs.P0303
import N7.Kernel.CoverProofs.P0304
import N7.Kernel.CoverProofs.P0305
import N7.Kernel.CoverProofs.P0306
import N7.Kernel.CoverProofs.P0307
import N7.Kernel.PositiveGroups.G0165
import N7.Kernel.PositiveGroups.G0166
import N7.Kernel.PositiveGroups.G0211
import N7.Kernel.PositiveGroups.G0212
import N7.Kernel.PositiveGroups.G0248
import N7.Kernel.PositiveGroups.G0249
import N7.Kernel.PositiveGroups.G0278
import N7.Kernel.PositiveGroups.G0279
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3096 : BoxMajorant Geometry.b3096 := by
  exact PositiveLeaves.L922.bound

theorem bound3094 : BoxMajorant Geometry.b3094 := by
  exact PositiveLeaves.L927.bound

theorem bound3091 : BoxMajorant Geometry.b3091 := by
  exact PositiveLeaves.L937.bound

theorem bound3090 : BoxMajorant Geometry.b3090 := by
  exact PositiveLeaves.L939.bound

theorem bound3089 : BoxMajorant Geometry.b3089 := by
  exact PositiveLeaves.L940.bound

theorem bound2706 : BoxMajorant Geometry.b2706 := by
  exact PositiveLeaves.L894.bound

theorem bound2704 : BoxMajorant Geometry.b2704 := by
  exact PositiveLeaves.L897.bound

theorem bound2698 : BoxMajorant Geometry.b2698 := by
  exact PositiveLeaves.L917.bound

theorem bound2696 : BoxMajorant Geometry.b2696 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2696.Widths)
  · have he : Geometry.b2696.half 2 false=Geometry.b3095 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3095
  · have he : Geometry.b2696.half 2 true=Geometry.b3096 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3096

theorem bound2695 : BoxMajorant Geometry.b2695 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2695.Widths)
  · have he : Geometry.b2695.half 2 false=Geometry.b3093 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3093
  · have he : Geometry.b2695.half 2 true=Geometry.b3094 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3094

theorem bound2694 : BoxMajorant Geometry.b2694 := by
  exact PositiveLeaves.L934.bound

theorem bound2693 : BoxMajorant Geometry.b2693 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2693.Widths)
  · have he : Geometry.b2693.half 2 false=Geometry.b3091 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3091
  · have he : Geometry.b2693.half 2 true=Geometry.b3092 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3092

theorem bound2692 : BoxMajorant Geometry.b2692 := by
  exact PositiveLeaves.L938.bound

theorem bound2691 : BoxMajorant Geometry.b2691 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2691.Widths)
  · have he : Geometry.b2691.half 2 false=Geometry.b3089 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3089
  · have he : Geometry.b2691.half 2 true=Geometry.b3090 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3090

theorem bound2344 : BoxMajorant Geometry.b2344 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2344.Widths)
  · have he : Geometry.b2344.half 1 false=Geometry.b2705 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2705
  · have he : Geometry.b2344.half 1 true=Geometry.b2706 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2706

theorem bound2343 : BoxMajorant Geometry.b2343 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2343.Widths)
  · have he : Geometry.b2343.half 1 false=Geometry.b2703 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2703
  · have he : Geometry.b2343.half 1 true=Geometry.b2704 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2704

theorem bound2342 : BoxMajorant Geometry.b2342 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2342.Widths)
  · have he : Geometry.b2342.half 1 false=Geometry.b2701 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2701
  · have he : Geometry.b2342.half 1 true=Geometry.b2702 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2702

theorem bound2341 : BoxMajorant Geometry.b2341 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2341.Widths)
  · have he : Geometry.b2341.half 1 false=Geometry.b2699 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2699
  · have he : Geometry.b2341.half 1 true=Geometry.b2700 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2700

theorem bound2340 : BoxMajorant Geometry.b2340 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2340.Widths)
  · have he : Geometry.b2340.half 1 false=Geometry.b2697 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2697
  · have he : Geometry.b2340.half 1 true=Geometry.b2698 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2698

theorem bound2339 : BoxMajorant Geometry.b2339 := by
  exact PositiveLeaves.L920.bound

theorem bound2338 : BoxMajorant Geometry.b2338 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2338.Widths)
  · have he : Geometry.b2338.half 1 false=Geometry.b2695 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2695
  · have he : Geometry.b2338.half 1 true=Geometry.b2696 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2696

theorem bound2337 : BoxMajorant Geometry.b2337 := by
  exact PositiveLeaves.L933.bound

theorem bound2336 : BoxMajorant Geometry.b2336 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2336.Widths)
  · have he : Geometry.b2336.half 1 false=Geometry.b2693 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2693
  · have he : Geometry.b2336.half 1 true=Geometry.b2694 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2694

theorem bound2335 : BoxMajorant Geometry.b2335 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2335.Widths)
  · have he : Geometry.b2335.half 1 false=Geometry.b2691 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2691
  · have he : Geometry.b2335.half 1 true=Geometry.b2692 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2692

theorem bound1796 : BoxMajorant Geometry.b1796 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1796.Widths)
  · have he : Geometry.b1796.half 0 false=Geometry.b2343 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2343
  · have he : Geometry.b1796.half 0 true=Geometry.b2344 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2344

theorem bound1795 : BoxMajorant Geometry.b1795 := by
  exact PositiveLeaves.L900.bound

theorem bound1794 : BoxMajorant Geometry.b1794 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1794.Widths)
  · have he : Geometry.b1794.half 0 false=Geometry.b2341 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2341
  · have he : Geometry.b1794.half 0 true=Geometry.b2342 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2342

theorem bound1793 : BoxMajorant Geometry.b1793 := by
  exact PositiveLeaves.L916.bound

theorem bound1792 : BoxMajorant Geometry.b1792 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1792.Widths)
  · have he : Geometry.b1792.half 0 false=Geometry.b2339 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2339
  · have he : Geometry.b1792.half 0 true=Geometry.b2340 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2340

theorem bound1791 : BoxMajorant Geometry.b1791 := by
  exact PositiveLeaves.L921.bound

theorem bound1790 : BoxMajorant Geometry.b1790 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1790.Widths)
  · have he : Geometry.b1790.half 0 false=Geometry.b2337 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2337
  · have he : Geometry.b1790.half 0 true=Geometry.b2338 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2338

theorem bound1789 : BoxMajorant Geometry.b1789 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1789.Widths)
  · have he : Geometry.b1789.half 0 false=Geometry.b2335 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2335
  · have he : Geometry.b1789.half 0 true=Geometry.b2336 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2336

theorem bound1252 : BoxMajorant Geometry.b1252 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1252.Widths)
  · have he : Geometry.b1252.half 2 false=Geometry.b1795 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1795
  · have he : Geometry.b1252.half 2 true=Geometry.b1796 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1796

theorem bound1251 : BoxMajorant Geometry.b1251 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1251.Widths)
  · have he : Geometry.b1251.half 2 false=Geometry.b1793 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1793
  · have he : Geometry.b1251.half 2 true=Geometry.b1794 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1794

theorem bound1250 : BoxMajorant Geometry.b1250 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1250.Widths)
  · have he : Geometry.b1250.half 2 false=Geometry.b1791 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1791
  · have he : Geometry.b1250.half 2 true=Geometry.b1792 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1792

theorem bound1249 : BoxMajorant Geometry.b1249 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1249.Widths)
  · have he : Geometry.b1249.half 2 false=Geometry.b1789 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1789
  · have he : Geometry.b1249.half 2 true=Geometry.b1790 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1790

theorem bound906 : BoxMajorant Geometry.b906 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b906.Widths)
  · have he : Geometry.b906.half 1 false=Geometry.b1251 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1251
  · have he : Geometry.b906.half 1 true=Geometry.b1252 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1252

theorem bound905 : BoxMajorant Geometry.b905 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b905.Widths)
  · have he : Geometry.b905.half 1 false=Geometry.b1249 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1249
  · have he : Geometry.b905.half 1 true=Geometry.b1250 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1250

theorem bound621 : BoxMajorant Geometry.b621 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b621.Widths)
  · have he : Geometry.b621.half 0 false=Geometry.b905 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound905
  · have he : Geometry.b621.half 0 true=Geometry.b906 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound906

end N7.Kernel.Cover
