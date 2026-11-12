import N7.Witness
import Mathlib.Tactic

set_option autoImplicit false

namespace N7.Analysis

def normSum (z : Configuration) : ℝ := ∑ i, Complex.normSq (z i)
def discriminant (z : Configuration) : ℝ :=
  ∏ p ∈ pairs, Complex.normSq (z p.1 - z p.2)

theorem normSum_eq_energy (z : Configuration) : normSum z = energy z := by
  simp only [normSum, energy, Chalk.energy, Complex.normSq_eq_norm_sq]

theorem discriminant_eq_delta (z : Configuration) : discriminant z = delta z := by
  simp only [discriminant, pairs, Finset.prod_filter, Complex.normSq_eq_norm_sq]
  rw [show (Finset.univ : Finset (Fin 7 × Fin 7)) =
    Finset.univ ×ˢ Finset.univ from Finset.univ_product_univ.symm]
  rw [Finset.prod_product]
  rfl

end N7.Analysis
