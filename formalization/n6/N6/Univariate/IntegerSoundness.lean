import N6.Univariate.IntegerCore
import Mordell.Interval

set_option autoImplicit false

namespace N6.IntegerCover

def Bounds.Mem (b : Bounds) (x : ℝ) : Prop :=
  (b.lo : ℝ) ≤ (b.den : ℝ)*x ∧ (b.den : ℝ)*x ≤ (b.hi : ℝ)

noncomputable def eval (p : List ℤ) (x : ℝ) : ℝ :=
  p.foldr (fun a y => (a : ℝ) + x*y) 0

private theorem fixed_mul_bounds {l h y : ℝ} (hl : l ≤ y) (hh : y ≤ h) (a : ℝ) :
    min (a*l) (a*h) ≤ a*y ∧ a*y ≤ max (a*l) (a*h) := by
  rcases le_total 0 a with ha | ha
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hl ha),
      (mul_le_mul_of_nonneg_left hh ha).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hh ha),
      (mul_le_mul_of_nonpos_left hl ha).trans (le_max_left _ _)⟩

theorem Bounds.mem_mul {a b : Bounds} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.mul b).Mem (x*y) := by
  have hl := fixed_mul_bounds hy.1 hy.2 (a.lo : ℝ)
  have hh := fixed_mul_bounds hy.1 hy.2 (a.hi : ℝ)
  have hxy := fixed_mul_bounds hx.1 hx.2 ((b.den : ℝ)*y)
  simp only [mul_comm ((b.den : ℝ)*y)] at hxy
  have hc :
      min (min ((a.lo : ℝ)*b.lo) ((a.lo : ℝ)*b.hi))
          (min ((a.hi : ℝ)*b.lo) ((a.hi : ℝ)*b.hi)) ≤
          ((a.den : ℝ)*x)*((b.den : ℝ)*y) ∧
      ((a.den : ℝ)*x)*((b.den : ℝ)*y) ≤
        max (max ((a.lo : ℝ)*b.lo) ((a.lo : ℝ)*b.hi))
          (max ((a.hi : ℝ)*b.lo) ((a.hi : ℝ)*b.hi)) := by
    constructor
    · apply le_trans _ hxy.1
      exact le_min ((min_le_left _ _).trans hl.1) ((min_le_right _ _).trans hh.1)
    · apply le_trans hxy.2
      exact max_le (hl.2.trans (le_max_left _ _)) (hh.2.trans (le_max_right _ _))
  unfold Bounds.Mem Bounds.mul
  push_cast
  convert hc using 1 <;> ring

theorem Bounds.mem_addConst (a : ℤ) {b : Bounds} {x : ℝ} (hx : b.Mem x) :
    (b.addConst a).Mem ((a : ℝ)+x) := by
  unfold Bounds.Mem Bounds.addConst at *
  push_cast
  constructor <;> nlinarith [hx.1, hx.2]

theorem range_sound (p : List ℤ) (b : Bounds) (x : ℝ) (hx : b.Mem x) :
    (range p b).Mem (eval p x) := by
  induction p with
  | nil => simp [range, eval, Bounds.Mem, Bounds.point]
  | cons a p ih => exact Bounds.mem_addConst a (Bounds.mem_mul hx ih)

theorem range_den_pos (p : List ℤ) (b : Bounds) (hb : 0 < b.den) :
    0 < (range p b).den := by
  induction p with
  | nil => change 0 < 1; decide
  | cons a p ih => exact Nat.mul_pos hb ih

theorem split_covers (b : Bounds) (x : ℝ) (hx : b.Mem x) :
    b.left.Mem x ∨ b.right.Mem x := by
  rcases le_total ((2 : ℝ)*b.den*x) ((b.lo : ℝ)+b.hi) with ht | ht
  · left
    unfold Bounds.Mem Bounds.left
    push_cast
    constructor <;> nlinarith [hx.1, hx.2]
  · right
    unfold Bounds.Mem Bounds.right
    push_cast
    constructor <;> nlinarith [hx.1, hx.2]

theorem Cover.sound (c : Cover) (p v : List ℤ) (vden limit : ℕ) :
    ∀ b x, 0 < b.den → c.check p v vden limit b = true → b.Mem x → eval p x = 0 →
      -((limit*vden : ℕ) : ℝ) < eval v x ∧ eval v x < ((limit*vden : ℕ) : ℝ) := by
  induction c with
  | leaf =>
    intro b x hb hc hx hp
    have hc : 0 < (range p b).lo ∨ (range p b).hi < 0 ∨
        (-(limit*vden*(range v b).den : ℤ) < (range v b).lo ∧
         (range v b).hi < (limit*vden*(range v b).den : ℤ)) := of_decide_eq_true hc
    have he := range_sound p b x hx
    rcases hc with hl | hr | hv
    · have hl' : (0 : ℝ) < (range p b).lo := by exact_mod_cast hl
      simp only [Bounds.Mem, hp, mul_zero] at he
      exact False.elim (not_lt_of_ge he.1 hl')
    · have hr' : ((range p b).hi : ℝ) < 0 := by exact_mod_cast hr
      simp only [Bounds.Mem, hp, mul_zero] at he
      exact False.elim (not_lt_of_ge he.2 hr')
    · have he := range_sound v b x hx
      have hlo : -((limit*vden : ℕ) : ℝ)*(range v b).den < ((range v b).lo : ℝ) := by
        have hraw : -(((limit*vden*(range v b).den : ℕ) : ℝ)) <
            ((range v b).lo : ℝ) := by exact_mod_cast hv.1
        simpa only [Nat.cast_mul, neg_mul] using hraw
      have hhi : ((range v b).hi : ℝ) < ((limit*vden : ℕ) : ℝ)*(range v b).den := by
        exact_mod_cast hv.2
      have hd : (0 : ℝ) < (range v b).den := by exact_mod_cast range_den_pos v b hb
      constructor
      · nlinarith [hlo.trans_le he.1]
      · nlinarith [he.2.trans_lt hhi]
  | split a c ha hc =>
    intro b x hb hcheck hx hp
    have hh : a.check p v vden limit b.left = true ∧
        c.check p v vden limit b.right = true := by
      simpa only [Cover.check, Bool.and_eq_true] using hcheck
    rcases split_covers b x hx with hl | hr
    · exact ha _ x (Nat.mul_pos (by decide) hb) hh.1 hl hp
    · exact hc _ x (Nat.mul_pos (by decide) hb) hh.2 hr hp

#print axioms range_sound
#print axioms Cover.sound
end N6.IntegerCover
