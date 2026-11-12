import Eight.ClosedCover
import Eight.Statement

namespace MordellEight

def squareLower (lo hi : ℚ) : ℚ := if 0<lo then lo^2 else if hi<0 then hi^2 else 0

theorem squareLower_sound (lo hi : ℚ) {x : ℝ} (hx : (lo:ℝ)≤x ∧ x≤(hi:ℝ)) :
    (squareLower lo hi:ℝ)≤x^2 := by
  unfold squareLower
  split_ifs with hl hh
  · have h : (0:ℝ)<lo := by exact_mod_cast hl
    push_cast
    nlinarith [hx.1]
  · have h : (hi:ℝ)<0 := by exact_mod_cast hh
    push_cast
    nlinarith [hx.2]
  · simpa using sq_nonneg x

/-- Strict rejection only; equality at a physical domain boundary is retained. -/
def outsideCheck (b : ClosedBox 3) : Bool := decide
  (b.hi 0+b.hi 1-2*b.lo 2<2/7 ∨
   b.hi 0*b.hi 1<squareLower (b.lo 2) (b.hi 2) ∨ b.hi 1<b.lo 0)

theorem outsideCheck_sound (b : ClosedBox 3) (hc : outsideCheck b=true)
    {x : Fin 3 → ℝ} (hx : b.Contains x)
    (hd : PairDomain (x 0) (x 1) (x 2)) (hcanonical : x 0≤x 1) : False := by
  have h : b.hi 0+b.hi 1-2*b.lo 2<2/7 ∨
      b.hi 0*b.hi 1<squareLower (b.lo 2) (b.hi 2) ∨ b.hi 1<b.lo 0 :=
    of_decide_eq_true hc
  rcases h with hdist|hprod|horder
  · have h : ((b.hi 0+b.hi 1-2*b.lo 2:ℚ):ℝ)<((2/7:ℚ):ℝ) := by exact_mod_cast hdist
    push_cast at h
    linarith [(hx 0).2,(hx 1).2,(hx 2).1,hd.2.2.2.2.2]
  · have h : (b.hi 0:ℝ)*(b.hi 1:ℝ)<(squareLower (b.lo 2) (b.hi 2):ℝ) := by
      exact_mod_cast hprod
    have hp := mul_le_mul (hx 0).2 (hx 1).2 hd.2.1 (hd.1.trans (hx 0).2)
    have ht := squareLower_sound _ _ (hx 2)
    linarith [hd.2.2.2.2.1]
  · have h : (b.hi 1:ℝ)<(b.lo 0:ℝ) := by exact_mod_cast horder
    linarith [(hx 0).1,(hx 1).2]

end MordellEight
