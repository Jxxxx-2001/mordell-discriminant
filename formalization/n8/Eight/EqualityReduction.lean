import Eight.UpperReduction
import Eight.HeptagonShape

namespace MordellEight
open Finset
set_option maxHeartbeats 0

/-- The inverse equality classification, still explicitly conditional on the full domain inequality. -/
theorem centerHeptagon_of_equality_of_domainMajorant (hbound : DomainMajorant) {z : Configuration}
    (hz : energy z=8) (he : delta z=sharpConstant) : CenterHeptagon z := by
  have hm := equality_maximum_of_domainMajorant hbound he
  have hi := normalized_injective (maximum_injective hm)
  have hk := equality_momentVectors_of_domainMajorant hbound hz he
  have hr := kernel_zero_radius_classification (normalized z) (hk 0)
  have hp (k : ℕ) (hk0 : 0<k) (hk8 : k<7) : (∑ i,(normalized z i)^k)=0 := by
    have hkn : (⟨k,hk8⟩ : Fin 7)≠0 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero] at hv
      omega
    rw [←momentVector_first (normalized z) ⟨k,hk8⟩ hkn,hk]
    rfl
  exact normalized_shape_to_centerHeptagon z
    (binary_power_sums_shape (normalized z) (normalized_energy hz) hi hr hp)

/-- Full geometric iff reduction. DomainMajorant is not yet instantiated by a complete cover proof. -/
theorem equality_iff_of_domainMajorant (hbound : DomainMajorant) (z : Configuration) (hz : energy z=8) :
    delta z=sharpConstant ↔ CenterHeptagon z :=
  ⟨centerHeptagon_of_equality_of_domainMajorant hbound hz,fun h => (centerHeptagon_attains h).2⟩


end MordellEight
