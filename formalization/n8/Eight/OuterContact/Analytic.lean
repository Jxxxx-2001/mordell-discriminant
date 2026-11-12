import Eight.ContactJets
import Eight.HornerBounds
import Eight.Checks.IntervalMatrix

namespace MordellEight.OuterContact
open Checks Matrix Set GapAnalytic
set_option maxHeartbeats 0

def rationalCenter (q : ℚ) : Fin 3 → ℝ := ![1,1,(q:ℝ)]
def InCube (q r : ℚ) (x : Fin 3 → ℝ) : Prop := ∀ i, |x i-rationalCenter q i|≤(r:ℝ)
def inverseBounds (q r : ℚ) : QInterval := ⟨1/(2-2*q+4*r)^2,1/(2-2*q-4*r)^2⟩
def ddQ : Fin 3 → ℚ := ![1,1,-2]

def algebraicCenterCheck (j : Fin 4) (q r : ℚ) : Bool :=
  decide (0≤r ∧ q-r≤(contactT j).bound.lo ∧ (contactT j).bound.hi≤q+r)

theorem algebraicCenterCheck_sound (j : Fin 4) (hj : j≠0) (q r : ℚ)
    (h : algebraicCenterCheck j q r=true) : InCube q r (contactCenter j) := by
  have hc := of_decide_eq_true h
  have hr : (0:ℝ)≤(r:ℝ) := by exact_mod_cast hc.1
  have hb := AlgebraicCoeff.bound_sound (contactT j)
  have hl : (q:ℝ)-(r:ℝ)≤((contactT j).bound.lo:ℝ) := by exact_mod_cast hc.2.1
  have hh : ((contactT j).bound.hi:ℝ)≤(q:ℝ)+(r:ℝ) := by exact_mod_cast hc.2.2
  have ht : |(contactT j).real-(q:ℝ)|≤(r:ℝ) := abs_le.mpr
    ⟨by linarith [hb.1],by linarith [hb.2]⟩
  intro i
  fin_cases i
  · fin_cases j <;> simp_all [contactCenter,rationalCenter,contactU,AlgebraicCoeff.one_real]
  · simpa [contactCenter,rationalCenter,contactV,AlgebraicCoeff.one_real] using hr
  · simpa [contactCenter,rationalCenter,Matrix.cons_val_two] using ht

theorem cube_distance_bounds {q r : ℚ} {x : Fin 3 → ℝ} (hx : InCube q r x) :
    ((2-2*q-4*r:ℚ):ℝ)≤distance x ∧ distance x≤((2-2*q+4*r:ℚ):ℝ) := by
  have hu := abs_le.mp (hx 0)
  have hv := abs_le.mp (hx 1)
  have ht := abs_le.mp (hx 2)
  norm_num [rationalCenter,Matrix.cons_val_two] at hu hv ht
  dsimp [distance]
  push_cast
  constructor <;> linarith

theorem cube_distance_pos {q r : ℚ} (hp : 0<2-2*q-4*r) {x : Fin 3 → ℝ}
    (hx : InCube q r x) : 0<distance x :=
  lt_of_lt_of_le (by exact_mod_cast hp) (cube_distance_bounds hx).1

theorem inverseBounds_sound {q r : ℚ} (hp : 0<2-2*q-4*r) {x : Fin 3 → ℝ}
    (hx : InCube q r x) : (inverseBounds q r).Contains (1/(distance x)^2) := by
  have h := cube_distance_bounds hx
  have hd := cube_distance_pos hp hx
  have hlo : (0:ℝ)<((2-2*q-4*r:ℚ):ℝ) := by exact_mod_cast hp
  have hhi : (0:ℝ)<((2-2*q+4*r:ℚ):ℝ) := hd.trans_le h.2
  have sl : (((2-2*q-4*r:ℚ):ℝ))^2≤(distance x)^2 := by nlinarith [h.1]
  have sh : (distance x)^2≤(((2-2*q+4*r:ℚ):ℝ))^2 := by nlinarith [h.2]
  have lo := one_div_le_one_div_of_le (sq_pos_of_pos hd) sh
  have hi := one_div_le_one_div_of_le (sq_pos_of_pos hlo) sl
  simpa only [inverseBounds,QInterval.Contains,Rat.cast_div,Rat.cast_one,
    Rat.cast_pow,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat] using And.intro lo hi

theorem cube_line {q r : ℚ} {c x : Fin 3 → ℝ} (hc : InCube q r c) (hx : InCube q r x)
    {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : InCube q r (line c (x-c) s) := by
  intro i
  have hci := abs_le.mp (hc i)
  have hxi := abs_le.mp (hx i)
  apply abs_le.mpr
  change -(r:ℝ)≤c i+s*(x i-c i)-rationalCenter q i ∧
    c i+s*(x i-c i)-rationalCenter q i≤(r:ℝ)
  constructor <;> nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hxi.1),
    mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hci.1),
    mul_nonneg hs.1 (sub_nonneg.mpr hxi.2),
    mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hci.2)]

theorem hessian_bounds_sound {q r : ℚ} (hp : 0<2-2*q-4*r)
    (polynomials : Fin 3 → Fin 3 → DenseKernel)
    (he : ∀ i j x, (polynomials i j).real (x 0-1) (x 1-1) (x 2-(q:ℝ))=
      eval3 (partialPoly (partialPoly exactMajorant i) j) x)
    {x : Fin 3 → ℝ} (hx : InCube q r x) (i j : Fin 3) :
    (((polynomials i j).bound r).add ((inverseBounds q r).scale (ddQ i*ddQ j))).Contains
      (hessian exactMajorant x i j) := by
  have hu : |x 0-1|≤(r:ℝ) := by simpa [rationalCenter] using hx 0
  have hv : |x 1-1|≤(r:ℝ) := by simpa [rationalCenter] using hx 1
  have ht : |x 2-(q:ℝ)|≤(r:ℝ) := by simpa [rationalCenter,Matrix.cons_val_two] using hx 2
  have hb := DenseKernel.bound_sound r (polynomials i j) _ _ _ hu hv ht
  rw [he] at hb
  have h := QInterval.add_sound hb
    (QInterval.scale_sound (ddQ i*ddQ j) (inverseBounds_sound hp hx))
  have hc (k : Fin 3) : (ddQ k:ℝ)=dd k := by fin_cases k <;> norm_num [ddQ,dd,Matrix.cons_val_two]
  convert h using 1
  dsimp [hessian]
  push_cast
  rw [hc,hc]
  ring

theorem cube_gap_nonneg (j : Fin 4) (hj : j≠0) {q r : ℚ}
    (hp : 0<2-2*q-4*r) (hc : algebraicCenterCheck j q r=true)
    (hh : ∀ x, InCube q r x → (hessian exactMajorant x).PosDef)
    {x : Fin 3 → ℝ} (hx : InCube q r x) :
    Real.log (distance x)≤exactMajorant.real (x 0) (x 1) (x 2) := by
  have hcenter := algebraicCenterCheck_sound j hj q r hc
  have hg : 0≤∑ i,gradient exactMajorant (contactCenter j) i*(x i-contactCenter j i) := by
    simp [gradient_at_outer_contact j hj]
  have h := gap_nonneg_of_segment exactMajorant (contactCenter j) x (gap_at_contact j) hg
    (fun s hs => (cube_distance_pos hp (cube_line hcenter hx hs)).ne')
    (fun s hs => (hh _ (cube_line hcenter hx hs)).posSemidef)
  exact sub_nonneg.mp h

end MordellEight.OuterContact
