import Eight.RootBounds.Remaining
import Eight.EqualityReduction
import Eight.Witness

namespace MordellEight

/-- Unconditional eight-point upper bound, using the full closed-domain certificate. -/
theorem upper_8 : UpperStatement := by
  intro z hz
  exact upper_of_domainMajorant RootBounds.domainMajorant z hz

/-- Complete equality classification at the sharp eight-point constant. -/
theorem equality_8 : EqualityStatement := by
  intro z hz
  exact equality_iff_of_domainMajorant RootBounds.domainMajorant z hz

theorem complete_8 : CompleteStatement := ⟨upper_8,equality_8⟩

#print axioms upper_8
#print axioms equality_8
#print axioms witness_8
end MordellEight
