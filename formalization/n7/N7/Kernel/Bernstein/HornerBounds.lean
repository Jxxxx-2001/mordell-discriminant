-- Adapted from the checked Eight.HornerBounds general semantics.
import N7.Kernel.Bernstein.DenseKernel
import N7.Kernel.Bernstein.CoefficientBounds

namespace N7.Kernel
open Checks
set_option maxHeartbeats 0

def hornerBound {A : Type} (bounds : A → QInterval) (r : ℚ) : List A → QInterval
  | [] => QInterval.zero
  | a::p =>
      let b := bounds a
      let tail := hornerBound bounds r p
      (⟨b.lo-r*tail.norm,b.hi+r*tail.norm⟩ : QInterval).round

theorem hornerBound_sound {A : Type} (bounds : A → QInterval) (e : A → ℝ)
    (hs : ∀ a, (bounds a).Contains (e a)) (r : ℚ) (p : List A) (x : ℝ)
    (hx : |x| ≤ (r : ℝ)) : (hornerBound bounds r p).Contains (horner e p x) := by
  induction p with
  | nil => norm_num [QInterval.Contains,QInterval.zero,hornerBound,horner]
  | cons a p ih =>
    apply QInterval.round_sound
    have hp := QInterval.norm_sound ih
    have hm : |x*horner e p x| ≤ (r : ℝ)*(hornerBound bounds r p).norm := by
      rw [abs_mul]
      exact mul_le_mul hx hp (abs_nonneg _) ((abs_nonneg x).trans hx)
    have hh := abs_le.mp hm
    dsimp [QInterval.Contains,horner]
    push_cast
    constructor <;> linarith [(hs a).1,(hs a).2,hh.1,hh.2]

def DenseKernel.bound (r : ℚ) (p : DenseKernel) : QInterval :=
  hornerBound (hornerBound (hornerBound KernelCoeff.bound r) r) r p

theorem DenseKernel.bound_sound (r : ℚ) (p : DenseKernel) (u v t : ℝ)
    (hu : |u| ≤ (r : ℝ)) (hv : |v| ≤ (r : ℝ)) (ht : |t| ≤ (r : ℝ)) :
    (p.bound r).Contains (p.real u v t) := by
  apply hornerBound_sound _ _ ?_ r p u hu
  intro q
  apply hornerBound_sound _ _ ?_ r q v hv
  intro s
  exact hornerBound_sound _ _ KernelCoeff.bound_sound r s t ht

end N7.Kernel
