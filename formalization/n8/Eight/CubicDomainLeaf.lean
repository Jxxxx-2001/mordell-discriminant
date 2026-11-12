import Eight.CubicLeaf

namespace MordellEight.CubicDomainLeaf
open CubicLeaf FixedTensor IntegerCube RationalCube

noncomputable def affine (b : ClosedBox 3) (i : Fin 3) (z : ℝ) : ℝ :=
  (b.hi i - b.lo i : ℚ) * z + b.lo i

noncomputable def penalty (g o k u v t : ℝ) : ℝ :=
  g * (u*v - t^2) + o * (v-u) + k * (u+v-2*t-2/7)

theorem penalty_nonneg {x : Fin 3 → ℝ} (hd : CanonicalDomain x)
    {g o k : ℝ} (hg : 0 ≤ g) (ho : 0 ≤ o) (hk : 0 ≤ k) :
    0 ≤ penalty g o k (x 0) (x 1) (x 2) := by
  exact add_nonneg (add_nonneg
    (mul_nonneg hg (sub_nonneg.mpr hd.1.2.2.2.2.1))
    (mul_nonneg ho (sub_nonneg.mpr hd.2)))
    (mul_nonneg hk (sub_nonneg.mpr hd.1.2.2.2.2.2))

theorem majorant {p : Cube} {b : ClosedBox 3} (hw : b.Widths)
    (hm : TensorMinorant b (decode p)) (a l : ℚ) (A : Int) (ts : List Term)
    (g o k : ℚ) (hA : 0 < A) (ha : 0 < (a : ℝ)) (hl : Real.log (a : ℝ) ≤ (l : ℝ))
    (hg : 0 ≤ (g : ℝ)) (ho : 0 ≤ (o : ℝ)) (hk : 0 ≤ (k : ℝ))
    (ident : ∀ u v t : ℝ, value u v t ts = -((A:ℝ)*2^80) *
      (upper l (dist b u v t / a - 1) + penalty g o k (affine b 0 u) (affine b 1 v) (affine b 2 t)))
    (check : nonneg (gap p A ts) = true) : BoxMajorant b := by
  apply majorant_of_value hw hm a l A ts hA ha hl ?_ check
  intro x _ hd
  have hcoord (i : Fin 3) : affine b i (b.coord x i) = x i :=
    affine_unit_coordinate _ _ _ (hw i)
  rw [ident, dist_coords b hw x, hcoord 0, hcoord 1, hcoord 2]
  apply mul_le_mul_of_nonpos_left (le_add_of_nonneg_right (penalty_nonneg hd hg ho hk))
  have hscale : 0 ≤ (A : ℝ) * 2^80 := mul_nonneg (by exact_mod_cast hA.le) (by positivity)
  exact neg_nonpos.mpr hscale

end MordellEight.CubicDomainLeaf
