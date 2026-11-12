import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace MordellEight

structure ClosedBox (n : ℕ) where
  lo : Fin n → ℚ
  hi : Fin n → ℚ

def ClosedBox.Contains {n : ℕ} (b : ClosedBox n) (x : Fin n → ℝ) : Prop :=
  ∀ i, (b.lo i : ℝ) ≤ x i ∧ x i ≤ (b.hi i : ℝ)

def ClosedBox.left {n : ℕ} (b : ClosedBox n) (axis : Fin n) (cut : ℚ) : ClosedBox n :=
  ⟨b.lo, Function.update b.hi axis cut⟩

def ClosedBox.right {n : ℕ} (b : ClosedBox n) (axis : Fin n) (cut : ℚ) : ClosedBox n :=
  ⟨Function.update b.lo axis cut, b.hi⟩

theorem ClosedBox.split_contains {n : ℕ} (b : ClosedBox n) (axis : Fin n) (cut : ℚ)
    {x : Fin n → ℝ} (hx : b.Contains x) :
    (b.left axis cut).Contains x ∨ (b.right axis cut).Contains x := by
  rcases le_total (x axis) (cut : ℝ) with h | h
  · left
    intro i
    by_cases hi : i = axis
    · subst i
      exact ⟨(hx axis).1, by simpa [ClosedBox.left] using h⟩
    · simpa [ClosedBox.Contains, ClosedBox.left, Function.update_of_ne hi] using hx i
  · right
    intro i
    by_cases hi : i = axis
    · subst i
      exact ⟨by simpa [ClosedBox.right] using h, (hx axis).2⟩
    · simpa [ClosedBox.Contains, ClosedBox.right, Function.update_of_ne hi] using hx i

inductive ClosedTree (n : ℕ) where
  | leaf : Nat → ClosedBox n → ClosedTree n
  | split : Fin n → ℚ → ClosedTree n → ClosedTree n → ClosedTree n

def ClosedTree.leaves {n : ℕ} : ClosedTree n → List (Nat × ClosedBox n)
  | .leaf id b => [(id,b)]
  | .split _ _ l r => l.leaves ++ r.leaves

/-- This checker certifies the geometry of the partition only. -/
def ClosedTree.check {n : ℕ} (b : ClosedBox n) : ClosedTree n → Bool
  | .leaf _ c => decide (∀ i, c.lo i = b.lo i ∧ c.hi i = b.hi i)
  | .split axis cut l r =>
      decide (b.lo axis ≤ cut ∧ cut ≤ b.hi axis) &&
      l.check (b.left axis cut) && r.check (b.right axis cut)

theorem ClosedTree.check_sound {n : ℕ} (tree : ClosedTree n) :
    ∀ b x, tree.check b = true → b.Contains x →
      ∃ id c, (id,c) ∈ tree.leaves ∧ c.Contains x := by
  induction tree with
  | leaf id c =>
    intro b x hc hx
    have he : ∀ i, c.lo i = b.lo i ∧ c.hi i = b.hi i := of_decide_eq_true hc
    refine ⟨id,c,by simp [ClosedTree.leaves],?_⟩
    intro i
    simpa only [(he i).1,(he i).2] using hx i
  | split axis cut l r hl hr =>
    intro b x hc hx
    have hh : (decide (b.lo axis ≤ cut ∧ cut ≤ b.hi axis) = true ∧ l.check (b.left axis cut) = true) ∧
        r.check (b.right axis cut) = true := by
      simpa only [ClosedTree.check, Bool.and_eq_true] using hc
    have hleft := hh.1.2
    rcases b.split_contains axis cut hx with hxl | hxr
    · obtain ⟨id,c,hm,hc⟩ := hl _ _ hleft hxl
      exact ⟨id,c,by simp [ClosedTree.leaves,hm],hc⟩
    · obtain ⟨id,c,hm,hc⟩ := hr _ _ hh.2 hxr
      exact ⟨id,c,by simp [ClosedTree.leaves,hm],hc⟩

/-- Leaf mathematics must be supplied by actual theorems, in addition to the geometry check. -/
theorem ClosedTree.forall_of_check {n : ℕ} (tree : ClosedTree n) (b : ClosedBox n)
    (P : (Fin n → ℝ) → Prop) (hc : tree.check b = true)
    (hleaves : ∀ id c, (id,c) ∈ tree.leaves → ∀ x, c.Contains x → P x) :
    ∀ x, b.Contains x → P x := by
  intro x hx
  obtain ⟨id,c,hm,hmem⟩ := tree.check_sound b x hc hx
  exact hleaves id c hm x hmem

end MordellEight
