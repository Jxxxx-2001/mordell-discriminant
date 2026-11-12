import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.CoverGeometry.G0086
import N7.Kernel.PositiveGroups.G0450
import N7.Kernel.PositiveGroups.G0461
import N7.Kernel.PositiveGroups.G0469
import N7.Kernel.PositiveGroups.G0470
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5504 : BoxMajorant Geometry.b5504 := by
  exact PositiveLeaves.L446.bound

theorem bound5503 : BoxMajorant Geometry.b5503 := by
  exact PositiveLeaves.L447.bound

theorem bound5502 : BoxMajorant Geometry.b5502 := by
  exact PositiveLeaves.L448.bound

theorem bound5501 : BoxMajorant Geometry.b5501 := by
  exact PositiveLeaves.L449.bound

theorem bound5500 : BoxMajorant Geometry.b5500 := by
  exact PositiveLeaves.L450.bound

theorem bound5499 : BoxMajorant Geometry.b5499 := by
  exact PositiveLeaves.L451.bound

theorem bound5370 : BoxMajorant Geometry.b5370 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5370.Widths)
  · have he : Geometry.b5370.half 2 false=Geometry.b5503 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5503
  · have he : Geometry.b5370.half 2 true=Geometry.b5504 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5504

theorem bound5369 : BoxMajorant Geometry.b5369 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5369.Widths)
  · have he : Geometry.b5369.half 2 false=Geometry.b5501 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5501
  · have he : Geometry.b5369.half 2 true=Geometry.b5502 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5502

theorem bound5368 : BoxMajorant Geometry.b5368 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5368.Widths)
  · have he : Geometry.b5368.half 2 false=Geometry.b5499 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5499
  · have he : Geometry.b5368.half 2 true=Geometry.b5500 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5500

theorem bound5367 : BoxMajorant Geometry.b5367 := by
  exact PositiveLeaves.L452.bound

theorem bound5260 : BoxMajorant Geometry.b5260 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5260.Widths)
  · have he : Geometry.b5260.half 1 false=Geometry.b5369 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5369
  · have he : Geometry.b5260.half 1 true=Geometry.b5370 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5370

theorem bound5259 : BoxMajorant Geometry.b5259 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5259.Widths)
  · have he : Geometry.b5259.half 1 false=Geometry.b5367 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5367
  · have he : Geometry.b5259.half 1 true=Geometry.b5368 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5368

theorem bound5058 : BoxMajorant Geometry.b5058 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5058.Widths)
  · have he : Geometry.b5058.half 0 false=Geometry.b5259 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5259
  · have he : Geometry.b5058.half 0 true=Geometry.b5260 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5260

theorem bound5057 : BoxMajorant Geometry.b5057 := by
  exact PositiveLeaves.L453.bound

theorem bound5056 : BoxMajorant Geometry.b5056 := by
  exact PositiveLeaves.L454.bound

theorem bound5055 : BoxMajorant Geometry.b5055 := by
  exact PositiveLeaves.L455.bound

theorem bound4682 : BoxMajorant Geometry.b4682 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4682.Widths)
  · have he : Geometry.b4682.half 2 false=Geometry.b5057 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5057
  · have he : Geometry.b4682.half 2 true=Geometry.b5058 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5058

theorem bound4681 : BoxMajorant Geometry.b4681 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4681.Widths)
  · have he : Geometry.b4681.half 2 false=Geometry.b5055 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5055
  · have he : Geometry.b4681.half 2 true=Geometry.b5056 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5056

theorem bound4414 : BoxMajorant Geometry.b4414 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4414.Widths)
  · have he : Geometry.b4414.half 1 false=Geometry.b4681 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4681
  · have he : Geometry.b4414.half 1 true=Geometry.b4682 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4682

end N7.Kernel.Cover
