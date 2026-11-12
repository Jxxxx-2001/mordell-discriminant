import N7.Kernel.UpperReduction
import N7.Kernel.Shape

set_option autoImplicit false
namespace N7.Kernel

variable (Q : Fin 6 → Matrix (Fin 4) (Fin 4) ℝ)

theorem centeredHexagon_of_equality_of_majorant (hQ : ∀ k, (Q k).PosDef)
    (hbound : MaximumMajorant Q) {z : Configuration}
    (hz : energy z=7) (he : delta z=sharpConstant) : IsCenteredHexagon z := by
  have hvec := equality_momentVectors_of_majorant Q hQ hbound hz he
  apply centeredHexagon_of_normalized_moments hz
    (kernel_zero_radius_classification (normalized z) (hvec 0))
  intro k hk hk6
  have hne : (⟨k,hk6⟩ : Fin 6)≠0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero] at hv
    omega
  have h := congrFun (hvec ⟨k,hk6⟩) 0
  rw [momentVector_first (normalized z) ⟨k,hk6⟩ hne] at h
  exact h

theorem equality_iff_of_majorant (hQ : ∀ k, (Q k).PosDef)
    (hbound : MaximumMajorant Q) {z : Configuration} (hz : energy z=7) :
    delta z=sharpConstant ↔ IsCenteredHexagon z := by
  constructor
  · exact centeredHexagon_of_equality_of_majorant Q hQ hbound hz
  · exact fun h => (centeredHexagon_sharp h).2

#print axioms centeredHexagon_of_equality_of_majorant
#print axioms equality_iff_of_majorant
end N7.Kernel
