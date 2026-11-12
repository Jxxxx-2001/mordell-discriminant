import Eight.SeparableCubic
import Eight.CubicDomainLeaf

namespace MordellEight.AffineGramLeaf
open CubicLeaf CubicDomainLeaf FixedTensor IntegerCube RationalCube
open SeparableCubic (Coeff StageU StageV coeff computeU computeV)
set_option maxHeartbeats 0

/-- Six nonnegative endpoint coefficients define a nonnegative affine weight
on the normalized unit cube. -/
noncomputable def weight (lo hi : Fin 3 → ℚ) (s : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ((lo i : ℝ)*(1-s i)+(hi i : ℝ)*s i)

theorem weight_nonneg (lo hi : Fin 3 → ℚ) (s : Fin 3 → ℝ)
    (hlo : ∀ i, 0≤(lo i : ℝ)) (hhi : ∀ i, 0≤(hi i : ℝ))
    (hs : ∀ i, 0≤s i ∧ s i≤1) : 0≤weight lo hi s := by
  apply Finset.sum_nonneg
  intro i _
  exact add_nonneg (mul_nonneg (hlo i) (sub_nonneg.mpr (hs i).2))
    (mul_nonneg (hhi i) (hs i).1)

/-- Gram weight in unit coordinates; domain constraints in physical coordinates. -/
noncomputable def penalty (b : ClosedBox 3) (lo hi : Fin 3 → ℚ) (o k : ℚ)
    (s : Fin 3 → ℝ) : ℝ :=
  CubicDomainLeaf.penalty (weight lo hi s) o k
    (CubicDomainLeaf.affine b 0 (s 0)) (CubicDomainLeaf.affine b 1 (s 1)) (CubicDomainLeaf.affine b 2 (s 2))

theorem penalty_nonneg {b : ClosedBox 3} (hw : b.Widths)
    {x : Fin 3 → ℝ} (hx : b.Contains x) (hd : CanonicalDomain x)
    (lo hi : Fin 3 → ℚ) (o k : ℚ)
    (hlo : ∀ i, 0≤(lo i : ℝ)) (hhi : ∀ i, 0≤(hi i : ℝ))
    (ho : 0≤(o : ℝ)) (hk : 0≤(k : ℝ)) :
    0≤penalty b lo hi o k (fun i => b.coord x i) := by
  have hcoord (i : Fin 3) : CubicDomainLeaf.affine b i (b.coord x i)=x i :=
    affine_unit_coordinate _ _ _ (hw i)
  unfold penalty
  rw [hcoord 0,hcoord 1,hcoord 2]
  exact CubicDomainLeaf.penalty_nonneg hd
    (weight_nonneg lo hi _ hlo hhi (fun i => ClosedBox.coord_unit hw hx i)) ho hk

private theorem coord_vector (b : ClosedBox 3) (x : Fin 3 → ℝ) :
    ![b.coord x 0,b.coord x 1,b.coord x 2]=(fun i => b.coord x i) := by
  funext i
  fin_cases i <;> rfl

/-- General penalty bridge. `hq` may be proved just from unit-coordinate
bounds, or may also use the physical canonical domain (as Gram penalties do).
No polynomial form or sign assumption outside that domain is required. -/
theorem majorant_of_penalty {p : Cube} {b : ClosedBox 3} (hw : b.Widths)
    (hm : TensorMinorant b (decode p)) (a l : ℚ) (A : Int) (ts : List Term)
    (c : Coeff) (pu : StageU) (pv : StageV)
    (hc : ∀ e f k, c e f k=coeff ts e f k)
    (hu : ∀ i f k, pu i f k=computeU c i f k)
    (hv : ∀ i j k, pv i j k=computeV pu i j k)
    (q : (Fin 3 → ℝ) → ℝ)
    (hA : 0<A) (ha : 0<(a : ℝ)) (hl : Real.log (a : ℝ)≤(l : ℝ))
    (hq : ∀ x, b.Contains x → CanonicalDomain x → 0≤q (fun i => b.coord x i))
    (ident : ∀ u v t : ℝ, value u v t ts = -((A:ℝ)*2^80)*
      (upper l (dist b u v t/a-1)+q ![u,v,t]))
    (check : nonneg (SeparableCubic.gap p A pv)=true) : BoxMajorant b := by
  apply SeparableCubic.majorant_of_value hw hm a l A ts c pu pv hc hu hv hA ha hl ?_ check
  intro x hx hd
  rw [ident,dist_coords b hw x,coord_vector]
  apply mul_le_mul_of_nonpos_left (le_add_of_nonneg_right (hq x hx hd))
  have hscale : 0≤(A:ℝ)*2^80 := mul_nonneg (by exact_mod_cast hA.le) (by positivity)
  exact neg_nonpos.mpr hscale

/-- Separable cubic leaf with a six-coefficient affine Gram multiplier. All
matrix, logarithm, polynomial-identity and integer-gap checks remain explicit. -/
theorem majorant {p : Cube} {b : ClosedBox 3} (hw : b.Widths)
    (hm : TensorMinorant b (decode p)) (a l : ℚ) (A : Int) (ts : List Term)
    (c : Coeff) (pu : StageU) (pv : StageV)
    (hc : ∀ e f k, c e f k=coeff ts e f k)
    (hu : ∀ i f k, pu i f k=computeU c i f k)
    (hv : ∀ i j k, pv i j k=computeV pu i j k)
    (lo hi : Fin 3 → ℚ) (o k : ℚ)
    (hA : 0<A) (ha : 0<(a : ℝ)) (hl : Real.log (a : ℝ)≤(l : ℝ))
    (hlo : ∀ i, 0≤(lo i : ℝ)) (hhi : ∀ i, 0≤(hi i : ℝ))
    (ho : 0≤(o : ℝ)) (hk : 0≤(k : ℝ))
    (ident : ∀ u v t : ℝ, value u v t ts = -((A:ℝ)*2^80)*
      (upper l (dist b u v t/a-1)+penalty b lo hi o k ![u,v,t]))
    (check : nonneg (SeparableCubic.gap p A pv)=true) : BoxMajorant b := by
  apply majorant_of_penalty hw hm a l A ts c pu pv hc hu hv
    (penalty b lo hi o k) hA ha hl ?_ ident check
  intro x hx hd
  exact penalty_nonneg hw hx hd lo hi o k hlo hhi ho hk

#print axioms majorant_of_penalty
#print axioms majorant
end MordellEight.AffineGramLeaf
