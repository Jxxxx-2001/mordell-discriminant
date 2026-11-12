import Chalk.Products

set_option autoImplicit false

namespace N7

abbrev Configuration := Fin 7 → ℂ

noncomputable abbrev energy (z : Configuration) : ℝ := Chalk.energy z
noncomputable abbrev delta (z : Configuration) : ℝ := Chalk.delta z
noncomputable def sharpConstant : ℝ := (7 : ℝ)^21 / 6^15

noncomputable def witnessScale : ℂ := (Real.sqrt ((7 : ℝ)/6) : ℂ)
noncomputable def witnessRoot : ℂ := Complex.exp (2*Real.pi*Complex.I/6)
noncomputable def unitWitness : Configuration :=
  Fin.cases 0 (fun j : Fin 6 => witnessRoot^j.val)
noncomputable def sharpWitness : Configuration := fun i => witnessScale * unitWitness i

/-- The fixed explicit witness, up to a rotation and a relabelling; no translation. -/
def IsCenteredHexagon (z : Configuration) : Prop :=
  ∃ u : ℂ, ‖u‖ = 1 ∧ ∃ σ : Equiv.Perm (Fin 7),
    ∀ i, z (σ i) = u * sharpWitness i

def pairs : Finset (Fin 7 × Fin 7) := Finset.univ.filter (fun p => p.1 < p.2)

theorem pairs_card : pairs.card = 21 := by decide

theorem delta_nonneg (z : Configuration) : 0 ≤ delta z := by
  unfold delta Chalk.delta
  exact Finset.prod_nonneg fun _ _ =>
    Finset.prod_nonneg fun _ _ => by split_ifs <;> positivity

end N7
