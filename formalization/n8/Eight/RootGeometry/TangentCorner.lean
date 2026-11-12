import Eight.RootGeometry.Common

namespace MordellEight.RootGeometry.TangentCorner

/-- Saturation of the Gram inequality at strictly positive coordinate upper bounds. -/
theorem coordinates {x : Fin 3 → ℝ} {p q s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) (hsq : s^2=p*q)
    (hu : x 0 ≤ p) (hv : x 1 ≤ q)
    (ht : s^2 ≤ (x 2)^2) (hd : CanonicalDomain x) :
    x 0=p ∧ x 1=q := by
  have hu0 : 0 ≤ x 0 := hd.1.1
  have hv0 : 0 ≤ x 1 := hd.1.2.1
  have hgram : (x 2)^2 ≤ x 0*x 1 := hd.1.2.2.2.2.1
  have hmulq : x 0*x 1 ≤ x 0*q := mul_le_mul_of_nonneg_left hv hu0
  have hmulp : x 0*x 1 ≤ p*x 1 := mul_le_mul_of_nonneg_right hu hv0
  constructor
  · apply le_antisymm hu
    by_contra! h
    have := mul_lt_mul_of_pos_right h hq
    linarith
  · apply le_antisymm hv
    by_contra! h
    have := mul_lt_mul_of_pos_left h hp
    linarith

/-- Positive tangent corner: only upper u/v faces and the lower t face are needed. -/
theorem positive (b : ClosedBox 3) {p q s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) (hsq : s^2=p*q)
    (bhu : (b.hi 0 : ℝ) ≤ p) (bhv : (b.hi 1 : ℝ) ≤ q)
    (blt : s ≤ (b.lo 2 : ℝ))
    {x : Fin 3 → ℝ} (hx : b.Contains x) (hd : CanonicalDomain x) :
    x 0=p ∧ x 1=q ∧ x 2=s := by
  have hu : x 0 ≤ p := le_trans (hx 0).2 bhu
  have hv : x 1 ≤ q := le_trans (hx 1).2 bhv
  have ht : s ≤ x 2 := le_trans blt (hx 2).1
  have htsq : s^2 ≤ (x 2)^2 := by nlinarith [sq_nonneg (x 2 - s), sq_nonneg (x 2 + s), mul_nonneg (sub_nonneg.mpr ht) hs.le]
  obtain ⟨hu',hv'⟩ := coordinates hp hq hs hsq hu hv htsq hd
  refine ⟨hu',hv',?_⟩
  have hgram := hd.1.2.2.2.2.1
  rw [hu',hv', ←hsq] at hgram
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (le_antisymm hgram htsq) with h | h <;> linarith

/-- Negative tangent corner: only upper u/v faces and the upper t face are needed. -/
theorem negative (b : ClosedBox 3) {p q s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) (hsq : s^2=p*q)
    (bhu : (b.hi 0 : ℝ) ≤ p) (bhv : (b.hi 1 : ℝ) ≤ q)
    (bht : (b.hi 2 : ℝ) ≤ -s)
    {x : Fin 3 → ℝ} (hx : b.Contains x) (hd : CanonicalDomain x) :
    x 0=p ∧ x 1=q ∧ x 2= -s := by
  have hu : x 0 ≤ p := le_trans (hx 0).2 bhu
  have hv : x 1 ≤ q := le_trans (hx 1).2 bhv
  have ht : x 2 ≤ -s := le_trans (hx 2).2 bht
  have htsq : s^2 ≤ (x 2)^2 := by nlinarith [sq_nonneg (x 2 - s), sq_nonneg (x 2 + s), mul_nonneg (sub_nonneg.mpr ht) hs.le]
  obtain ⟨hu',hv'⟩ := coordinates hp hq hs hsq hu hv htsq hd
  refine ⟨hu',hv',?_⟩
  have hgram := hd.1.2.2.2.2.1
  rw [hu',hv', ←hsq] at hgram
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (le_antisymm hgram htsq) with h | h <;> linarith

#print axioms positive
#print axioms negative
end MordellEight.RootGeometry.TangentCorner
