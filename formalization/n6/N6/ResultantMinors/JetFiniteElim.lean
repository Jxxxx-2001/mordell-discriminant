import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
set_option autoImplicit false
namespace N6.ResultantMinors.JetFinite
theorem forallFin0 {P : Fin 0 → Prop}  : ∀ j, P j := by
  intro j; exact Fin.elim0 j
theorem forallFin1 {P : Fin 1 → Prop} (h0 : P 0) : ∀ j, P j := by
  intro j; fin_cases j <;> assumption
theorem forallFin2 {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ j, P j := by
  intro j; fin_cases j <;> assumption
theorem forallFin3 {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ j, P j := by
  intro j; fin_cases j <;> assumption
theorem forallFin4 {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ j, P j := by
  intro j; fin_cases j <;> assumption
theorem forallFin5 {P : Fin 5 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) : ∀ j, P j := by
  intro j; fin_cases j <;> assumption
theorem forallFin6 {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ j, P j := by
  intro j; fin_cases j <;> assumption
#print axioms forallFin4
end N6.ResultantMinors.JetFinite
