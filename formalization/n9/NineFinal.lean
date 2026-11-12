import Pilot.NineCompleteDomain
import Pilot.NineEqualityReduction
import Pilot.NineExplicitWitness

namespace MordellNine

theorem mordell9_upper (z : Fin 9 → ℂ) (hz : (∑ i, ‖z i‖ ^ 2) = 9) :
    discriminant z ≤ (9 : ℝ) ^ 36 / 8 ^ 28 :=
  upper_of_domainMajorant MordellPilot.Nine.CompleteDomain.majorant z hz

theorem mordell9_attainment (θ : ℝ) :
    (∑ i : Fin 9, ‖octagonWitness θ i‖ ^ 2) = 9 ∧
      discriminant (octagonWitness θ) = (9 : ℝ) ^ 36 / 8 ^ 28 :=
  explicit_attainment_9 θ

theorem mordell9_equality_iff (z : Fin 9 → ℂ) (hz : (∑ i, ‖z i‖ ^ 2) = 9) :
    discriminant z = (9 : ℝ) ^ 36 / 8 ^ 28 ↔
      ∃ θ : ℝ, ∃ σ : Equiv.Perm (Fin 9), z (σ 0) = 0 ∧ ∀ k : Fin 8,
        z (σ k.succ) = (Real.sqrt (9/8 : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((θ + 2 * Real.pi * (k.val : ℝ) / 8 : ℝ) : ℂ)) :=
  equality_iff_of_domainMajorant MordellPilot.Nine.CompleteDomain.majorant z hz

end MordellNine
