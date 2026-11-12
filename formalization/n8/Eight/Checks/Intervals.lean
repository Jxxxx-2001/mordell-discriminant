import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Ring

namespace MordellEight.Checks
set_option maxHeartbeats 0

structure QInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def QInterval.Contains (a : QInterval) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ a.hi
def QInterval.norm (a : QInterval) : ℚ := max |a.lo| |a.hi|
def QInterval.zero : QInterval := ⟨0,0⟩
def QInterval.add (a b : QInterval) : QInterval := ⟨a.lo+b.lo,a.hi+b.hi⟩
def QInterval.scale (r : ℚ) (a : QInterval) : QInterval :=
  if 0 ≤ r then ⟨r*a.lo,r*a.hi⟩ else ⟨r*a.hi,r*a.lo⟩
def QInterval.mul (a b : QInterval) : QInterval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

theorem mul_between (c x a b L U : ℝ) (hx : a ≤ x ∧ x ≤ b)
    (ha : L ≤ c*a ∧ c*a ≤ U) (hb : L ≤ c*b ∧ c*b ≤ U) : L ≤ c*x ∧ c*x ≤ U := by
  by_cases h : 0 ≤ c
  · have hl := mul_le_mul_of_nonneg_left hx.1 h
    have hu := mul_le_mul_of_nonneg_left hx.2 h
    exact ⟨ha.1.trans hl,hu.trans hb.2⟩
  · have hl := mul_le_mul_of_nonpos_left hx.2 (le_of_lt (lt_of_not_ge h))
    have hu := mul_le_mul_of_nonpos_left hx.1 (le_of_lt (lt_of_not_ge h))
    exact ⟨hb.1.trans hl,hu.trans ha.2⟩

theorem QInterval.mul_sound {a b : QInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x*y) := by
  have hc : ∀ z ∈ [a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi],
      (a.mul b).lo ≤ z ∧ z ≤ (a.mul b).hi := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;> simp [QInterval.mul,min_le_iff,le_max_iff]
  have hll : (a.mul b).Contains ((a.lo : ℝ)*(b.lo : ℝ)) := by
    have h := hc (a.lo*b.lo) (by simp)
    constructor <;> exact_mod_cast (by first | exact h.1 | exact h.2)
  have hlu : (a.mul b).Contains ((a.lo : ℝ)*(b.hi : ℝ)) := by
    have h := hc (a.lo*b.hi) (by simp)
    constructor <;> exact_mod_cast (by first | exact h.1 | exact h.2)
  have hul : (a.mul b).Contains ((a.hi : ℝ)*(b.lo : ℝ)) := by
    have h := hc (a.hi*b.lo) (by simp)
    constructor <;> exact_mod_cast (by first | exact h.1 | exact h.2)
  have huu : (a.mul b).Contains ((a.hi : ℝ)*(b.hi : ℝ)) := by
    have h := hc (a.hi*b.hi) (by simp)
    constructor <;> exact_mod_cast (by first | exact h.1 | exact h.2)
  have hl := mul_between (a.lo : ℝ) y _ _ _ _ hy hll hlu
  have hu := mul_between (a.hi : ℝ) y _ _ _ _ hy hul huu
  simpa only [QInterval.Contains,mul_comm] using
    mul_between y x _ _ _ _ hx (by simpa [mul_comm] using hl) (by simpa [mul_comm] using hu)

theorem QInterval.norm_sound {a : QInterval} {x : ℝ} (h : a.Contains x) :
    |x| ≤ (a.norm : ℝ) := by
  have h1 : |a.lo| ≤ a.norm := le_max_left _ _
  have h2 : |a.hi| ≤ a.norm := le_max_right _ _
  have h1' : |(a.lo : ℝ)| ≤ (a.norm : ℝ) := by exact_mod_cast h1
  have h2' : |(a.hi : ℝ)| ≤ (a.norm : ℝ) := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith [h.1,h.2,neg_le_abs (a.lo : ℝ),le_abs_self (a.hi : ℝ)]

theorem QInterval.add_sound {a b : QInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x+y) := by
  dsimp [QInterval.Contains,QInterval.add]
  push_cast
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem QInterval.scale_sound (r : ℚ) {a : QInterval} {x : ℝ} (h : a.Contains x) :
    (a.scale r).Contains ((r : ℝ)*x) := by
  unfold QInterval.scale
  split_ifs with hr
  · have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
    dsimp [QInterval.Contains]
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left h.1 hr',mul_le_mul_of_nonneg_left h.2 hr'⟩
  · have hr' : (r : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hr))
    dsimp [QInterval.Contains]
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left h.2 hr',mul_le_mul_of_nonpos_left h.1 hr'⟩

def roundDown (q : ℚ) : ℚ := (⌊q*(2^40 : ℚ)⌋ : ℚ)/(2^40 : ℚ)
def roundUp (q : ℚ) : ℚ := -roundDown (-q)

theorem roundDown_le (q : ℚ) : roundDown q ≤ q := by
  unfold roundDown
  apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 2^40)).mpr
  exact Int.floor_le _

theorem le_roundUp (q : ℚ) : q ≤ roundUp q := by
  have h := roundDown_le (-q)
  dsimp [roundUp]
  linarith

def QInterval.round (a : QInterval) : QInterval := ⟨roundDown a.lo,roundUp a.hi⟩
theorem QInterval.round_sound {a : QInterval} {x : ℝ} (h : a.Contains x) : a.round.Contains x := by
  have hl : (roundDown a.lo : ℝ) ≤ a.lo := by exact_mod_cast roundDown_le a.lo
  have hu : (a.hi : ℝ) ≤ roundUp a.hi := by exact_mod_cast le_roundUp a.hi
  exact ⟨hl.trans h.1,h.2.trans hu⟩


end MordellEight.Checks
