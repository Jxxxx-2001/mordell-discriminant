import Eight.RootTensor.BT
import Eight.BernsteinTensor

namespace MordellEight.RootTensor
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem lower_shape : lowerPolynomial.shapeCheck 12 12 6=true := by decide +kernel
theorem bu_shape : BU.shapeCheck 12 12 6=true := by decide +kernel
theorem bv_shape : BV.shapeCheck 12 12 6=true := by decide +kernel
theorem bt_shape : BT.shapeCheck 12 12 6=true := by decide +kernel

theorem bernstein_value (u v t : ℝ) : BT.bernEval 12 12 6 u v t=lowerPolynomial.real u v t :=
  RationalCube.bernEval_eq_power lowerPolynomial BU BV BT 12 12 6
    (RationalCube.shapeCheck_sound _ _ _ _ lower_shape)
    (RationalCube.shapeCheck_sound _ _ _ _ bu_shape)
    (RationalCube.shapeCheck_sound _ _ _ _ bv_shape) checkBU checkBV checkBT u v t

/-- A single root tensor lower bound, on the exact same auxiliary polynomial. -/
theorem unit_minorant (u v t : ℝ) (hu : 0≤u) (hv : 0≤v) (ht : 0≤t) :
    BT.bernEval 12 12 6 u v t≤exactMajorant.real
      ((box.hi 0-box.lo 0:ℚ)*u+box.lo 0)
      ((box.hi 1-box.lo 1:ℚ)*v+box.lo 1)
      ((box.hi 2-box.lo 2:ℚ)*t+box.lo 2) := by
  rw [bernstein_value]
  have h := RefinedBounds.lowerCheck_sound padded lowerPolynomial lower_checked u v t hu hv ht
  rw [←densePadCheck_sound T padded padded_checked u v t] at h
  rw [DenseKernel.affine_checked_real polynomial U V T _ _ _ _ _ _ checkU checkV checkT,
    polynomial_real] at h
  exact h

theorem box_widths : ∀ i,box.lo i<box.hi i := by decide +kernel

theorem box_minorant (x : Fin 3 → ℝ) (hx : box.Contains x) :
    BT.bernEval 12 12 6
      ((x 0-box.lo 0)/(box.hi 0-box.lo 0:ℚ))
      ((x 1-box.lo 1)/(box.hi 1-box.lo 1:ℚ))
      ((x 2-box.lo 2)/(box.hi 2-box.lo 2:ℚ))≤exactMajorant.real (x 0) (x 1) (x 2) := by
  have h := unit_minorant _ _ _
    (unit_coordinate_between _ _ (box_widths 0) (hx 0)).1
    (unit_coordinate_between _ _ (box_widths 1) (hx 1)).1
    (unit_coordinate_between _ _ (box_widths 2) (hx 2)).1
  rw [affine_unit_coordinate _ _ _ (box_widths 0),affine_unit_coordinate _ _ _ (box_widths 1),
    affine_unit_coordinate _ _ _ (box_widths 2)] at h
  exact h

end MordellEight.RootTensor
