import Eight.Checks.Intervals
import Eight.Constants

namespace MordellEight
open Checks

def alphaInterval : QInterval := ⟨alphaLo,alphaHi⟩
def alphaSquareInterval : QInterval := alphaInterval.mul alphaInterval
def logarithmInterval : Fin 3 → QInterval :=
  ![⟨-283663/1000000,-28366293/100000000⟩,
    ⟨44703111/50000000,22351557/25000000⟩,
    ⟨33387771/25000000,13355109/10000000⟩]

theorem alphaInterval_sound : alphaInterval.Contains alpha := alpha_bounds
theorem alphaSquareInterval_sound : alphaSquareInterval.Contains (alpha^2) := by
  simpa [alphaSquareInterval,pow_two] using
    QInterval.mul_sound alphaInterval_sound alphaInterval_sound

theorem logarithmInterval_sound (j : Fin 3) :
    (logarithmInterval j).Contains (logConstants j) := by
  fin_cases j
  · simpa [logarithmInterval,QInterval.Contains] using log0_bounds
  · simpa [logarithmInterval,QInterval.Contains] using log1_bounds
  · simpa [logarithmInterval,QInterval.Contains,Matrix.cons_val_two] using log2_bounds

def AlgebraicCoeff.bound (a : AlgebraicCoeff) : QInterval :=
  ((⟨a 0,a 0⟩ : QInterval).add (alphaInterval.scale (a 1))).add
    (alphaSquareInterval.scale (a 2))

theorem AlgebraicCoeff.bound_sound (a : AlgebraicCoeff) : a.bound.Contains a.real := by
  exact QInterval.add_sound
    (QInterval.add_sound ⟨le_rfl,le_rfl⟩ (QInterval.scale_sound _ alphaInterval_sound))
    (QInterval.scale_sound _ alphaSquareInterval_sound)

def KernelCoeff.bound (a : KernelCoeff) : QInterval :=
  (((a 0).bound.add ((a 1).bound.mul (logarithmInterval 0))).add
    ((a 2).bound.mul (logarithmInterval 1))).add
    ((a 3).bound.mul (logarithmInterval 2))

theorem KernelCoeff.real_explicit (a : KernelCoeff) :
    a.real = (a 0).real + (a 1).real*logConstants 0 +
      (a 2).real*logConstants 1 + (a 3).real*logConstants 2 := by
  simp [KernelCoeff.real,Fin.sum_univ_succ]
  ring

theorem KernelCoeff.bound_sound (a : KernelCoeff) : a.bound.Contains a.real := by
  rw [KernelCoeff.real_explicit]
  exact QInterval.add_sound
    (QInterval.add_sound
      (QInterval.add_sound (AlgebraicCoeff.bound_sound _)
        (QInterval.mul_sound (AlgebraicCoeff.bound_sound _) (logarithmInterval_sound 0)))
      (QInterval.mul_sound (AlgebraicCoeff.bound_sound _) (logarithmInterval_sound 1)))
    (QInterval.mul_sound (AlgebraicCoeff.bound_sound _) (logarithmInterval_sound 2))

end MordellEight
