import Eight.SeparableCubic
import Eight.CubicDomainLeaf

namespace MordellEight.SeparableDomainLeaf
open CubicLeaf CubicDomainLeaf FixedTensor IntegerCube RationalCube
open SeparableCubic (Coeff StageU StageV coeff computeU computeV)

theorem majorant {p : Cube} {b : ClosedBox 3} (hw : b.Widths)
    (hm : TensorMinorant b (decode p)) (a l : ℚ) (A : Int) (ts : List Term)
    (c : Coeff) (pu : StageU) (pv : StageV)
    (hc : ∀ e f k, c e f k = coeff ts e f k)
    (hu : ∀ i f k, pu i f k = computeU c i f k)
    (hv : ∀ i j k, pv i j k = computeV pu i j k)
    (g o k : ℚ) (hA : 0 < A) (ha : 0 < (a : ℝ)) (hl : Real.log (a : ℝ) ≤ (l : ℝ))
    (hg : 0 ≤ (g : ℝ)) (ho : 0 ≤ (o : ℝ)) (hk : 0 ≤ (k : ℝ))
    (ident : ∀ u v t : ℝ, value u v t ts = -((A:ℝ)*2^80) *
      (upper l (dist b u v t / a - 1) + penalty g o k (CubicDomainLeaf.affine b 0 u) (CubicDomainLeaf.affine b 1 v) (CubicDomainLeaf.affine b 2 t)))
    (check : nonneg (SeparableCubic.gap p A pv) = true) : BoxMajorant b := by
  apply SeparableCubic.majorant_of_value hw hm a l A ts c pu pv hc hu hv hA ha hl ?_ check
  intro x _ hd
  have hcoord (i : Fin 3) : CubicDomainLeaf.affine b i (b.coord x i) = x i :=
    affine_unit_coordinate _ _ _ (hw i)
  rw [ident, dist_coords b hw x, hcoord 0, hcoord 1, hcoord 2]
  apply mul_le_mul_of_nonpos_left (le_add_of_nonneg_right (penalty_nonneg hd hg ho hk))
  have hscale : 0 ≤ (A : ℝ) * 2^80 := mul_nonneg (by exact_mod_cast hA.le) (by positivity)
  exact neg_nonpos.mpr hscale

#print axioms majorant
end MordellEight.SeparableDomainLeaf
