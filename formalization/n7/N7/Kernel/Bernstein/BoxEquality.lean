import N7.Kernel.Bernstein.BoxCoordinates

set_option autoImplicit false
namespace N7.Kernel.ClosedBox

/-- Check normalized rational fields using only integer/natural Boolean equality. -/
def ratEqualCheck (p q : ℚ) : Bool := (p.num == q.num) && (p.den == q.den)

theorem ratEqualCheck_sound {p q : ℚ} (h : ratEqualCheck p q = true) : p = q := by
  have hh : (p.num == q.num) = true ∧ (p.den == q.den) = true := by
    simpa only [ratEqualCheck, Bool.and_eq_true] using h
  exact Rat.ext (eq_of_beq hh.1) (eq_of_beq hh.2)

def equalCheck {n : ℕ} (b c : ClosedBox n) : Bool :=
  (List.finRange n).all fun i =>
    ratEqualCheck (b.lo i) (c.lo i) && ratEqualCheck (b.hi i) (c.hi i)

theorem equalCheck_sound {n : ℕ} {b c : ClosedBox n}
    (h : equalCheck b c = true) : b = c := by
  have hi : ∀ i, b.lo i = c.lo i ∧ b.hi i = c.hi i := by
    simp only [equalCheck, List.all_eq_true] at h
    intro i
    have hh : ratEqualCheck (b.lo i) (c.lo i) = true ∧
        ratEqualCheck (b.hi i) (c.hi i) = true := by
      simpa only [Bool.and_eq_true] using h i (by simp)
    exact ⟨ratEqualCheck_sound hh.1, ratEqualCheck_sound hh.2⟩
  have hlo := funext fun i => (hi i).1
  have hhi := funext fun i => (hi i).2
  cases b
  cases c
  cases hlo
  cases hhi
  rfl

#print axioms equalCheck_sound
end N7.Kernel.ClosedBox
