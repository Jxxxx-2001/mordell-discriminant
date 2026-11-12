import N7.Kernel.Newton
import N7.Kernel.MaximumGeometry
import N7.BinomialClassification

set_option autoImplicit false
namespace N7.Kernel
open Finset Polynomial

theorem normalized_origin_of_binary {z : Configuration} (hz : energy z=7)
    (hr : ∀ i, ‖normalized z i‖^2=0 ∨ ‖normalized z i‖^2=1) :
    ∃ i, normalized z i=0 := by
  have hE := normalized_energy hz
  by_contra! hn
  have hones (i : Fin 7) : ‖normalized z i‖^2=1 :=
    (hr i).resolve_left (pow_ne_zero _ (norm_ne_zero_iff.mpr (hn i)))
  have htotal : energy (normalized z)=7 := by
    simp only [energy_eq_norm,hones]
    norm_num
  linarith

/-- The kernel's zero moments determine exactly the original rotation/permutation predicate. -/
theorem centeredHexagon_of_normalized_moments {z : Configuration} (hz : energy z=7)
    (hr : ∀ i, ‖normalized z i‖^2=0 ∨ ‖normalized z i‖^2=1)
    (hp : ∀ k : ℕ, 0<k → k<6 → (∑ i,(normalized z i)^k)=0) :
    IsCenteredHexagon z := by
  let e := (pointMultiset (normalized z)).esymm 6
  have hs : Analysis.rootProduct (normalized z)=X^7+C e*X :=
    rootProduct_shape _ hp (normalized_origin_of_binary hz hr)
  have he : e≠0 := by
    intro he
    have hall (i : Fin 7) : normalized z i=0 := by
      have h := rootProduct_root (normalized z) i
      rw [hs,he] at h
      simpa using h
    have hzero : energy (normalized z)=0 := by simp [energy_eq_norm,hall]
    have hE := normalized_energy hz
    linarith
  have hα : (Real.sqrt (6/7 : ℝ) : ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<6/7)).ne'
  exact centered_of_scaled_binomial z hz (Real.sqrt (6/7 : ℝ) : ℂ) e hα he hs

#print axioms centeredHexagon_of_normalized_moments
end N7.Kernel
