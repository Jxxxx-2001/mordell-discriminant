import N7.Kernel.Domain
import N7.Kernel.UpperReduction

set_option autoImplicit false
namespace N7.Kernel

/-- The continuous inequality to be certified on the entire necessary domain. -/
def DomainMajorant (Q : Fin 6 → Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ u v t : ℝ, PairDomain u v t →
    Real.log (u+v-2*t) ≤ majorantFromMatrices Q u v t

theorem maximum_majorant_of_domainMajorant
    (Q : Fin 6 → Matrix (Fin 4) (Fin 4) ℝ) (hbound : DomainMajorant Q) :
    MaximumMajorant Q := by
  intro z hz i j hij
  have h := hbound _ _ _ (maximum_pairDomain hz i j hij)
  rw [norm_sub_eq_realDot]
  exact h

theorem upper_of_domainMajorant
    (Q : Fin 6 → Matrix (Fin 4) (Fin 4) ℝ)
    (hQ : ∀ k, (Q k).PosDef) (hbound : DomainMajorant Q)
    {z : Configuration} (hz : energy z = 7) : delta z ≤ sharpConstant :=
  upper_of_majorant Q hQ (maximum_majorant_of_domainMajorant Q hbound) hz

#print axioms maximum_majorant_of_domainMajorant
#print axioms upper_of_domainMajorant
end N7.Kernel
