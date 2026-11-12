import Eight.RefinedConstants.L0
import Eight.RefinedConstants.L1
import Eight.RefinedConstants.L2
import Eight.HornerBounds
import Eight.RationalLower

namespace MordellEight.RefinedBounds
open Checks

def alphaSquare : QInterval := alphaRefined.mul alphaRefined
theorem alphaSquare_sound : alphaSquare.Contains (alpha^2) := by
  simpa [alphaSquare,pow_two] using QInterval.mul_sound alphaRefined_sound alphaRefined_sound

def logarithm : Fin 3 → QInterval :=
  ![RefinedConstants.L0.logBounds,RefinedConstants.L1.logBounds,RefinedConstants.L2.logBounds]
theorem logarithm_sound (j : Fin 3) : (logarithm j).Contains (logConstants j) := by
  fin_cases j
  · exact RefinedConstants.L0.logBounds_sound
  · exact RefinedConstants.L1.logBounds_sound
  · exact RefinedConstants.L2.logBounds_sound

def algebraic (a : AlgebraicCoeff) : QInterval :=
  ((⟨a 0,a 0⟩ : QInterval).add (alphaRefined.scale (a 1))).add (alphaSquare.scale (a 2))
theorem algebraic_sound (a : AlgebraicCoeff) : (algebraic a).Contains a.real :=
  QInterval.add_sound (QInterval.add_sound ⟨le_rfl,le_rfl⟩
    (QInterval.scale_sound _ alphaRefined_sound)) (QInterval.scale_sound _ alphaSquare_sound)

def coefficient (a : KernelCoeff) : QInterval :=
  (((algebraic (a 0)).add ((algebraic (a 1)).mul (logarithm 0))).add
    ((algebraic (a 2)).mul (logarithm 1))).add ((algebraic (a 3)).mul (logarithm 2))
theorem coefficient_sound (a : KernelCoeff) : (coefficient a).Contains a.real := by
  rw [KernelCoeff.real_explicit]
  exact QInterval.add_sound (QInterval.add_sound
    (QInterval.add_sound (algebraic_sound _) (QInterval.mul_sound (algebraic_sound _) (logarithm_sound 0)))
    (QInterval.mul_sound (algebraic_sound _) (logarithm_sound 1)))
    (QInterval.mul_sound (algebraic_sound _) (logarithm_sound 2))

def lowerCheck (p : DenseKernel) (q : RationalCube) : Bool :=
  zipCheck (zipCheck (zipCheck (fun c r => decide (r≤(coefficient c).lo)))) p q

/-- The selected dyadic precision is data; no 40-bit Horner rounding is used here. -/
theorem lowerCheck_sound (p : DenseKernel) (q : RationalCube) (hc : lowerCheck p q=true)
    (u v t : ℝ) (hu : 0≤u) (hv : 0≤v) (ht : 0≤t) : q.real u v t≤p.real u v t := by
  apply zipCheck_horner_le _ _ _ ?_ p q hc u hu
  intro a b hab
  apply zipCheck_horner_le _ _ _ ?_ a b hab v hv
  intro c d hcd
  apply zipCheck_horner_le _ _ _ ?_ c d hcd t ht
  intro e r her
  have h : r≤(coefficient e).lo := of_decide_eq_true her
  have hr : (r:ℝ)≤((coefficient e).lo:ℝ) := by exact_mod_cast h
  exact hr.trans (coefficient_sound e).1

def dense (r : ℚ) (p : DenseKernel) : QInterval :=
  hornerBound (hornerBound (hornerBound coefficient r) r) r p
theorem dense_sound (r : ℚ) (p : DenseKernel) (u v t : ℝ)
    (hu : |u|≤(r:ℝ)) (hv : |v|≤(r:ℝ)) (ht : |t|≤(r:ℝ)) :
    (dense r p).Contains (p.real u v t) := by
  apply hornerBound_sound _ _ ?_ r p u hu
  intro q
  apply hornerBound_sound _ _ ?_ r q v hv
  intro s
  exact hornerBound_sound _ _ coefficient_sound r s t ht

end MordellEight.RefinedBounds
