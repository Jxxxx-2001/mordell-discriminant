import N6.Univariate.Core
import Mordell.Interval

set_option autoImplicit false

namespace N6.Univariate

def Bounds.toInterval (b : Bounds) : Mordell.Interval := ⟨b.lo, b.hi⟩
def Bounds.Mem (b : Bounds) (x : ℝ) : Prop := b.toInterval.Mem x

noncomputable def eval (p : List ℚ) (x : ℝ) : ℝ :=
  p.foldr (fun a y => (a : ℝ) + x*y) 0

theorem range_sound (p : List ℚ) (b : Bounds) (x : ℝ) (hx : b.Mem x) :
    (range p b).Mem (eval p x) := by
  induction p with
  | nil => norm_num [range, eval, Bounds.Mem, Bounds.toInterval, Bounds.point,
      Mordell.Interval.Mem]
  | cons a p ih =>
    exact Mordell.Interval.mem_add (Mordell.Interval.mem_point a)
      (Mordell.Interval.mem_mul hx ih)

theorem split_covers (b : Bounds) (x : ℝ) (t : ℚ) (hx : b.Mem x) :
    (b.left t).Mem x ∨ (b.right t).Mem x := by
  rcases le_total x (t : ℝ) with ht | ht
  · left
    change (b.lo : ℝ) ≤ x ∧ x ≤ ((min b.hi t : ℚ) : ℝ)
    rw [Rat.cast_min]
    exact ⟨hx.1, le_min hx.2 ht⟩
  · right
    change ((max b.lo t : ℚ) : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)
    rw [Rat.cast_max]
    exact ⟨max_le hx.1 ht, hx.2⟩

theorem Cover.sound (c : Cover) (p v : List ℚ) (limit : ℚ) :
    ∀ b x, c.check p v limit b = true → b.Mem x → eval p x = 0 →
      -(limit : ℝ) < eval v x ∧ eval v x < limit := by
  induction c with
  | leaf =>
    intro b x hc hx hp
    have hc : 0 < (range p b).lo ∨ (range p b).hi < 0 ∨
        (-limit < (range v b).lo ∧ (range v b).hi < limit) := of_decide_eq_true hc
    rcases hc with hl | hr | hv
    · exact False.elim ((Mordell.Interval.nonzero_of_range (range_sound p b x hx)
        (Or.inl hl)) hp)
    · exact False.elim ((Mordell.Interval.nonzero_of_range (range_sound p b x hx)
        (Or.inr hr)) hp)
    · have he := range_sound v b x hx
      have hlo : -(limit : ℝ) < ((range v b).lo : ℝ) := by exact_mod_cast hv.1
      have hhi : ((range v b).hi : ℝ) < (limit : ℝ) := by exact_mod_cast hv.2
      exact ⟨hlo.trans_le he.1, he.2.trans_lt hhi⟩
  | split t a c ha hc =>
    intro b x hcheck hx hp
    have hh : a.check p v limit (b.left t) = true ∧
        c.check p v limit (b.right t) = true := by
      simpa only [Cover.check, Bool.and_eq_true] using hcheck
    rcases split_covers b x t hx with hl | hr
    · exact ha _ x hh.1 hl hp
    · exact hc _ x hh.2 hr hp

#print axioms range_sound
#print axioms Cover.sound

end N6.Univariate
