import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverGeometry.G0092
import N7.Kernel.PositiveGroups.G0472
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5944 : BoxMajorant Geometry.b5944 := by
  exact PositiveLeaves.L1286.bound

theorem bound5943 : BoxMajorant Geometry.b5943 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5943 2 (by decide +kernel) x hx hd ho).elim

theorem bound5942 : BoxMajorant Geometry.b5942 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5942.Widths)
  · have he : Geometry.b5942.half 1 false=Geometry.b5943 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5943
  · have he : Geometry.b5942.half 1 true=Geometry.b5944 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5944

theorem bound5941 : BoxMajorant Geometry.b5941 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5941 2 (by decide +kernel) x hx hd ho).elim

theorem bound5938 : BoxMajorant Geometry.b5938 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5938.Widths)
  · have he : Geometry.b5938.half 0 false=Geometry.b5941 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5941
  · have he : Geometry.b5938.half 0 true=Geometry.b5942 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5942

theorem bound5937 : BoxMajorant Geometry.b5937 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5937 2 (by decide +kernel) x hx hd ho).elim

theorem bound5930 : BoxMajorant Geometry.b5930 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5930.Widths)
  · have he : Geometry.b5930.half 2 false=Geometry.b5937 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5937
  · have he : Geometry.b5930.half 2 true=Geometry.b5938 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5938

theorem bound5929 : BoxMajorant Geometry.b5929 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5929 2 (by decide +kernel) x hx hd ho).elim

theorem bound5924 : BoxMajorant Geometry.b5924 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5924.Widths)
  · have he : Geometry.b5924.half 1 false=Geometry.b5929 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5929
  · have he : Geometry.b5924.half 1 true=Geometry.b5930 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5930

theorem bound5923 : BoxMajorant Geometry.b5923 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5923 2 (by decide +kernel) x hx hd ho).elim

theorem bound5876 : BoxMajorant Geometry.b5876 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5876.Widths)
  · have he : Geometry.b5876.half 0 false=Geometry.b5923 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5923
  · have he : Geometry.b5876.half 0 true=Geometry.b5924 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5924

theorem bound5875 : BoxMajorant Geometry.b5875 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5875 2 (by decide +kernel) x hx hd ho).elim

theorem bound5838 : BoxMajorant Geometry.b5838 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5838.Widths)
  · have he : Geometry.b5838.half 2 false=Geometry.b5875 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5875
  · have he : Geometry.b5838.half 2 true=Geometry.b5876 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5876

end N7.Kernel.Cover
