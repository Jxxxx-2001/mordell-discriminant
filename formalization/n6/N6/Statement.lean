import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option autoImplicit false

namespace N6
abbrev Configuration := Fin 6 → ℂ

def normSum (z : Configuration) : ℝ := ∑ i, Complex.normSq (z i)
def pairs : Finset (Fin 6 × Fin 6) := Finset.univ.filter (fun p => p.1 < p.2)
def discriminant (z : Configuration) : ℝ :=
  ∏ p ∈ pairs, Complex.normSq (z p.1 - z p.2)
noncomputable def sharpConstant : ℝ := (6 : ℝ)^15 / 5^10

-- The center is fixed at zero. The complex factor includes the required radius.
def IsCenteredPentagon (z : Configuration) : Prop :=
  ∃ u ω : ℂ, Complex.normSq u = (6 : ℝ)/5 ∧ IsPrimitiveRoot ω 5 ∧
    ∃ σ : Equiv.Perm (Fin 6), z (σ 0) = 0 ∧
      ∀ j : Fin 5, z (σ j.succ) = u * ω^j.val

theorem pairs_card : pairs.card = 15 := by decide
theorem discriminant_nonneg (z : Configuration) : 0 ≤ discriminant z := by
  unfold discriminant
  exact Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _

end N6
