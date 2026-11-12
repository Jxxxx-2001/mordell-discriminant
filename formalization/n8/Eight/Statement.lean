import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace MordellEight

abbrev Configuration := Fin 8 → ℂ
def energy (z : Configuration) : ℝ := ∑ i, Complex.normSq (z i)
def pairs : Finset (Fin 8 × Fin 8) := Finset.univ.filter (fun ij => ij.1 < ij.2)
def delta (z : Configuration) : ℝ :=
  ∏ ij ∈ pairs, Complex.normSq (z ij.1-z ij.2)
noncomputable def sharpConstant : ℝ := 8^28 / 7^21

noncomputable def heptagonConfig (θ : ℝ) : Configuration :=
  Fin.cases 0 (fun k : Fin 7 => (Real.sqrt (8/7) : ℂ) *
    Complex.exp (((θ + 2*Real.pi*(k.val : ℝ)/7 : ℝ) : ℂ)*Complex.I))

def CenterHeptagon (z : Configuration) : Prop :=
  ∃ θ : ℝ, ∃ σ : Equiv.Perm (Fin 8), ∀ i, z (σ i) = heptagonConfig θ i

/-- Target specifications only: neither the upper bound nor the equality iff is asserted here. -/
def UpperStatement : Prop := ∀ z : Configuration, energy z = 8 → delta z ≤ sharpConstant
def EqualityStatement : Prop := ∀ z : Configuration, energy z = 8 →
  (delta z = sharpConstant ↔ CenterHeptagon z)
def WitnessStatement : Prop := energy (heptagonConfig 0) = 8 ∧
  delta (heptagonConfig 0) = sharpConstant
def CompleteStatement : Prop := UpperStatement ∧ EqualityStatement

def PairDomain (u v t : ℝ) : Prop :=
  0 ≤ u ∧ 0 ≤ v ∧ u ≤ 965267/524288 ∧ v ≤ 965267/524288 ∧
  t^2 ≤ u*v ∧ 2/7 ≤ u+v-2*t

theorem pairs_card : pairs.card = 28 := by decide +kernel
theorem sharpConstant_pos : 0 < sharpConstant := by norm_num [sharpConstant]
theorem sharpConstant_scaled : sharpConstant = (7:ℝ)^7 * (8/7)^28 := by
  norm_num [sharpConstant]
theorem delta_nonneg (z : Configuration) : 0 ≤ delta z := by
  exact Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _

end MordellEight
