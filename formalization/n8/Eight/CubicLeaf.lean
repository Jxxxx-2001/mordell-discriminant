import Eight.CubicBasis
import Eight.CubicLog
import Eight.IntegerLeaf

namespace MordellEight.CubicLeaf
open FixedTensor IntegerCube RationalCube

structure Term where
  coeff : Int
  i : Fin 4
  j : Fin 4
  k : Fin 4
deriving DecidableEq

def sumControls : List Term → Cube
  | [] => []
  | t::ts => IntegerCube.add (IntegerCube.scale t.coeff (CubicBasis.controls t.i t.j t.k)) (sumControls ts)

noncomputable def value (u v w : ℝ) : List Term → ℝ
  | [] => 0
  | t::ts => t.coeff * (u^t.i.val * v^t.j.val * w^t.k.val) + value u v w ts

theorem sum_value (ts : List Term) (u v w : ℝ) :
    (raw (sumControls ts)).bernEval 12 12 6 u v w = value u v w ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [sumControls, raw_add, raw_scale, (bernSound 12 12 6 u v w).add,
      (bernSound 12 12 6 u v w).scale, CubicBasis.value, ih, value, Rat.cast_intCast]

def gap (p : Cube) (A : Int) (ts : List Term) : Cube :=
  IntegerCube.add (IntegerCube.scale A p) (sumControls ts)

noncomputable def dist (b : ClosedBox 3) (u v t : ℝ) : ℝ :=
  ((b.hi 0-b.lo 0 : ℚ)*u+b.lo 0) + ((b.hi 1-b.lo 1 : ℚ)*v+b.lo 1) -
  2*((b.hi 2-b.lo 2 : ℚ)*t+b.lo 2)

theorem dist_coords (b : ClosedBox 3) (hw : b.Widths) (x : Fin 3 → ℝ) :
    dist b (b.coord x 0) (b.coord x 1) (b.coord x 2) = x 0 + x 1 - 2*x 2 := by
  unfold dist ClosedBox.coord
  rw [affine_unit_coordinate _ _ _ (hw 0), affine_unit_coordinate _ _ _ (hw 1),
      affine_unit_coordinate _ _ _ (hw 2)]

noncomputable def upper (l y : ℝ) : ℝ := l + y - y^2/2 + y^3/3

theorem majorant_of_value {p : Cube} {b : ClosedBox 3} (hw : b.Widths)
    (hm : TensorMinorant b (decode p)) (a l : ℚ) (A : Int) (ts : List Term)
    (hA : 0 < A) (ha : 0 < (a : ℝ)) (hl : Real.log (a : ℝ) ≤ (l : ℝ))
    (hle : ∀ x, b.Contains x → CanonicalDomain x →
      value (b.coord x 0) (b.coord x 1) (b.coord x 2) ts ≤
        -((A:ℝ)*2^80) * upper l ((x 0+x 1-2*x 2)/a-1))
    (check : nonneg (gap p A ts) = true) : BoxMajorant b := by
  intro x hx hd
  have hn := bernEval_nonneg (raw (gap p A ts)) 12 12 6 (nonneg_sound _ check) _ _ _
    (ClosedBox.coord_unit hw hx 0) (ClosedBox.coord_unit hw hx 1) (ClosedBox.coord_unit hw hx 2)
  simp only [gap,raw_add,raw_scale,raw_decode p,(bernSound _ _ _ _ _ _).add,
    (bernSound _ _ _ _ _ _).scale,sum_value] at hn
  push_cast at hn
  have hpos : 0 < (A : ℝ) * 2^80 := mul_pos (by exact_mod_cast hA) (by positivity)
  have hgap : 0 ≤ (A : ℝ) * 2^80 *
      ((decode p).boxEval b x - upper l ((x 0+x 1-2*x 2)/a-1)) := by
    unfold boxEval
    linarith only [hn, hle x hx hd]
  have hdist : 0 < x 0+x 1-2*x 2 := lt_of_lt_of_le (by norm_num) hd.1.2.2.2.2.2
  exact (log_le_cubic hdist ha hl).trans
    ((sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hpos).mp hgap)).trans (hm x hx))

/-- The integer coefficient list is checked against the tangent in normalized
coordinates. A wrong exponent, scaling constant, box or log bound fails here. -/
theorem majorant {p : Cube} {b : ClosedBox 3} (hw : b.Widths)
    (hm : TensorMinorant b (decode p)) (a l : ℚ) (A : Int) (ts : List Term)
    (hA : 0 < A) (ha : 0 < (a : ℝ)) (hl : Real.log (a : ℝ) ≤ (l : ℝ))
    (ident : ∀ u v t : ℝ, value u v t ts =
       -((A:ℝ)*2^80) * upper l (dist b u v t / a - 1))
    (check : nonneg (gap p A ts) = true) : BoxMajorant b := by
  apply majorant_of_value hw hm a l A ts hA ha hl ?_ check
  intro x _ _
  rw [ident, dist_coords b hw x]

end MordellEight.CubicLeaf
