-- Adapted from the checked N6 analytic argument; see analysis/adapt_maximum.py.
import N7.Analysis.Directional

set_option autoImplicit false

namespace N7.Analysis

noncomputable def force (z : Configuration) (i : Fin 7) : ℂ :=
  ∑ j, if j = i then 0 else 1 / (z i - z j)

noncomputable def impulse (i : Fin 7) : Configuration :=
  fun j => if j = i then 1 else 0

theorem innerMoment_impulse (z : Configuration) (i : Fin 7) :
    innerMoment z (impulse i) = star (z i) := by
  simp [innerMoment, impulse]

theorem pairSum_impulse (z : Configuration) (i : Fin 7) :
    pairSum z (impulse i) = force z i := by
  have h10 : z 1 - z 0 = -(z 0 - z 1) := by ring
  have h20 : z 2 - z 0 = -(z 0 - z 2) := by ring
  have h30 : z 3 - z 0 = -(z 0 - z 3) := by ring
  have h40 : z 4 - z 0 = -(z 0 - z 4) := by ring
  have h50 : z 5 - z 0 = -(z 0 - z 5) := by ring
  have h60 : z 6 - z 0 = -(z 0 - z 6) := by ring
  have h21 : z 2 - z 1 = -(z 1 - z 2) := by ring
  have h31 : z 3 - z 1 = -(z 1 - z 3) := by ring
  have h41 : z 4 - z 1 = -(z 1 - z 4) := by ring
  have h51 : z 5 - z 1 = -(z 1 - z 5) := by ring
  have h61 : z 6 - z 1 = -(z 1 - z 6) := by ring
  have h32 : z 3 - z 2 = -(z 2 - z 3) := by ring
  have h42 : z 4 - z 2 = -(z 2 - z 4) := by ring
  have h52 : z 5 - z 2 = -(z 2 - z 5) := by ring
  have h62 : z 6 - z 2 = -(z 2 - z 6) := by ring
  have h43 : z 4 - z 3 = -(z 3 - z 4) := by ring
  have h53 : z 5 - z 3 = -(z 3 - z 5) := by ring
  have h63 : z 6 - z 3 = -(z 3 - z 6) := by ring
  have h54 : z 5 - z 4 = -(z 4 - z 5) := by ring
  have h64 : z 6 - z 4 = -(z 4 - z 6) := by ring
  have h65 : z 6 - z 5 = -(z 5 - z 6) := by ring
  unfold pairSum force impulse
  rw [pairs_explicit]
  repeat' (rw [Finset.sum_insert] <;> try decide)
  try simp only [Finset.sum_singleton]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i <;> simp [Fin.ext_iff, Fin.succ]
  all_goals simp only [h10, h20, h30, h40, h50, h60, h21, h31, h41, h51, h61, h32, h42, h52, h62, h43, h53, h63, h54, h64, h65, inv_neg, neg_div, one_div] <;> ring

theorem force_eq_sum_erase (z : Configuration) (i : Fin 7) :
    force z i = ∑ j ∈ Finset.univ.erase i, 1 / (z i - z j) := by
  unfold force
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [ite_true, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [if_neg (Finset.ne_of_mem_erase hj)]

theorem global_maximum_force_scaled {z : Configuration} (hz : IsGlobalMaximum z)
    (i : Fin 7) : (2 : ℂ) * force z i = 6 * star (z i) := by
  simpa only [pairSum_impulse, innerMoment_impulse] using
    global_maximum_pairSum hz (impulse i)

theorem global_maximum_force {z : Configuration} (hz : IsGlobalMaximum z)
    (i : Fin 7) : force z i = (3 : ℂ) * star (z i) := by
  have h := global_maximum_force_scaled hz i
  linear_combination (1 / 2 : ℂ) * h

theorem global_maximum_force_conj {z : Configuration} (hz : IsGlobalMaximum z)
    (i : Fin 7) : force z i = (3 : ℂ) * (starRingEnd ℂ) (z i) := by
  simpa only [Complex.star_def] using global_maximum_force hz i

theorem global_maximum_force_sum {z : Configuration} (hz : IsGlobalMaximum z)
    (i : Fin 7) :
    (∑ j ∈ Finset.univ.erase i, 1 / (z i - z j)) =
      (3 : ℂ) * (starRingEnd ℂ) (z i) := by
  rw [← force_eq_sum_erase]
  exact global_maximum_force_conj hz i

end N7.Analysis
