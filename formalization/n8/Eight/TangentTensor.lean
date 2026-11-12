import Eight.BoxCoordinates
import Eight.BernsteinBasis.One
import Eight.BernsteinBasis.U
import Eight.BernsteinBasis.V
import Eight.BernsteinBasis.T
import Eight.LogTangent

namespace MordellEight
open RationalCube
set_option maxHeartbeats 0

def distanceControls (b : ClosedBox 3) : RationalCube :=
  ops.add (ops.scale (b.lo 0+b.lo 1-2*b.lo 2) BernsteinBasis.One.controls)
    (ops.add (ops.scale (b.hi 0-b.lo 0) BernsteinBasis.U.controls)
      (ops.add (ops.scale (b.hi 1-b.lo 1) BernsteinBasis.V.controls)
        (ops.scale (-2*(b.hi 2-b.lo 2)) BernsteinBasis.T.controls)))

def gapControls (b : ClosedBox 3) (p : RationalCube) (a logUpper : ℚ) : RationalCube :=
  ops.add (ops.scale a p) (ops.add (ops.scale (-a*(logUpper-1)) BernsteinBasis.One.controls)
    (ops.scale (-1) (distanceControls b)))

theorem distanceControls_value (b : ClosedBox 3) (u v t : ℝ) :
    (distanceControls b).bernEval 12 12 6 u v t=
      ((b.hi 0-b.lo 0:ℚ)*u+b.lo 0)+((b.hi 1-b.lo 1:ℚ)*v+b.lo 1)-
      2*((b.hi 2-b.lo 2:ℚ)*t+b.lo 2) := by
  simp only [distanceControls,(bernSound 12 12 6 u v t).add,(bernSound 12 12 6 u v t).scale,
    BernsteinBasis.One.value,BernsteinBasis.U.value,BernsteinBasis.V.value,BernsteinBasis.T.value]
  push_cast
  ring

theorem gapControls_value (b : ClosedBox 3) (p : RationalCube) (a l : ℚ) (x : Fin 3 → ℝ)
    (hw : b.Widths) :
    (gapControls b p a l).boxEval b x=
      (a:ℝ)*p.boxEval b x-(a:ℝ)*((l:ℝ)-1)-(x 0+x 1-2*x 2) := by
  unfold boxEval gapControls
  rw [(bernSound _ _ _ _ _ _).add,(bernSound _ _ _ _ _ _).add,
    (bernSound _ _ _ _ _ _).scale,(bernSound _ _ _ _ _ _).scale,
    (bernSound _ _ _ _ _ _).scale,BernsteinBasis.One.value,distanceControls_value]
  simp only [ClosedBox.coord]
  rw [affine_unit_coordinate _ _ _ (hw 0),affine_unit_coordinate _ _ _ (hw 1),
    affine_unit_coordinate _ _ _ (hw 2)]
  push_cast
  ring

def tangentTensorCheck (b : ClosedBox 3) (p : RationalCube) (a logUpper : ℚ) : Bool :=
  (gapControls b p a logUpper).nonnegCheck

/-- Only the scalar logarithm certificate and coefficient inequalities are needed at a positive leaf. -/
theorem tangentTensorCheck_sound (b : ClosedBox 3) (p : RationalCube) (a l : ℚ)
    (hc : tangentTensorCheck b p a l=true) (hw : b.Widths)
    (ha : (0:ℝ)<(a:ℝ)) (hl : Real.log (a:ℝ)≤(l:ℝ))
    {x : Fin 3 → ℝ} (hx : b.Contains x) (hd : 0<x 0+x 1-2*x 2) :
    Real.log (x 0+x 1-2*x 2)≤p.boxEval b x := by
  have hn := bernEval_nonneg (gapControls b p a l) 12 12 6 hc _ _ _
    (ClosedBox.coord_unit hw hx 0) (ClosedBox.coord_unit hw hx 1) (ClosedBox.coord_unit hw hx 2)
  change 0≤(gapControls b p a l).boxEval b x at hn
  rw [gapControls_value b p a l x hw] at hn
  have ht := log_le_tangent hd ha hl
  have hm : (l:ℝ)-1+(x 0+x 1-2*x 2)/(a:ℝ)≤p.boxEval b x := by
    have hquot : (x 0+x 1-2*x 2)/(a:ℝ)≤p.boxEval b x-((l:ℝ)-1) :=
      (div_le_iff₀ ha).mpr (by nlinarith)
    linarith
  exact ht.trans hm

end MordellEight
