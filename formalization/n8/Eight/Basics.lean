import Eight.Statement
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

namespace MordellEight
open Finset Set

theorem energy_eq_norm (z : Configuration) : energy z = ∑ i, ‖z i‖^2 := by
  simp [energy,Complex.sq_norm]

theorem delta_eq_norm (z : Configuration) : delta z = pairs.prod (fun ij => ‖z ij.1-z ij.2‖^2) := by
  simp [delta,Complex.sq_norm]

def energyShell : Set Configuration := {z | energy z = 8}

theorem energy_nonneg (z : Configuration) : 0 ≤ energy z :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

theorem energy_continuous : Continuous energy := by
  simp only [funext energy_eq_norm]
  fun_prop

theorem delta_continuous : Continuous delta := by
  simp only [funext delta_eq_norm]
  fun_prop

theorem energyShell_compact : IsCompact energyShell := by
  have hclosed : IsClosed energyShell := isClosed_eq energy_continuous continuous_const
  apply (isCompact_closedBall (0 : Configuration) 3).of_isClosed_subset hclosed
  intro z hz
  have hE : energy z = 8 := hz
  have hbound (i : Fin 8) : ‖z i‖ ≤ 3 := by
    have hsq : ‖z i‖^2 ≤ 8 := by
      calc
        _ ≤ ∑ j : Fin 8, ‖z j‖^2 := Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        _ = 8 := by rw [←energy_eq_norm,hE]
    nlinarith [sq_nonneg (‖z i‖-3)]
  simp only [Metric.mem_closedBall,dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)).mpr hbound

theorem energyShell_nonempty : energyShell.Nonempty := by
  refine ⟨fun _ => (1 : ℂ),?_⟩
  norm_num [energyShell,energy]

theorem exists_global_maximum : ∃ z : Configuration, energy z=8 ∧
    ∀ w : Configuration, energy w=8 → delta w ≤ delta z := by
  obtain ⟨z,hz,hm⟩ := energyShell_compact.exists_isMaxOn energyShell_nonempty delta_continuous.continuousOn
  exact ⟨z,hz,fun w hw => hm hw⟩

theorem collision_delta_zero (z : Configuration) (i j : Fin 8)
    (hij : i < j) (he : z i=z j) : delta z=0 := by
  exact Finset.prod_eq_zero (show (i,j)∈pairs by simp [pairs,hij]) (by simp [he])

/-- A simple collinear positive witness, used only for collision exclusion. -/
noncomputable def positiveWitness : Configuration :=
  fun i => ((((i.val : ℝ)-7/2)*Real.sqrt (4/21 : ℝ) : ℝ) : ℂ)

theorem positiveWitness_energy : energy positiveWitness = 8 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4/21)
  rw [energy_eq_norm]
  unfold positiveWitness
  generalize he : Real.sqrt (4/21 : ℝ) = r
  have hr : r^2=(4/21 : ℝ) := by rw [←he]; exact hs
  norm_num [Fin.sum_univ_succ,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,hr]

theorem positiveWitness_injective : Function.Injective positiveWitness := by
  intro i j h
  have hs : Real.sqrt (4/21 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hr : ((i.val : ℝ)-7/2)*Real.sqrt (4/21 : ℝ) =
      ((j.val : ℝ)-7/2)*Real.sqrt (4/21 : ℝ) := Complex.ofReal_injective h
  have he := mul_right_cancel₀ hs hr
  have hv : (i.val : ℝ) = (j.val : ℝ) := by linarith
  apply Fin.ext
  exact_mod_cast hv

theorem positiveWitness_delta_pos : 0 < delta positiveWitness := by
  rw [delta_eq_norm]
  apply Finset.prod_pos
  intro ij hij
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  apply sub_ne_zero.mpr
  intro he
  exact (ne_of_lt (Finset.mem_filter.mp hij).2) (positiveWitness_injective he)

theorem maximum_delta_pos {z : Configuration}
    (hm : ∀ w : Configuration, energy w=8 → delta w ≤ delta z) :
    0 < delta z :=
  positiveWitness_delta_pos.trans_le (hm positiveWitness positiveWitness_energy)

theorem maximum_injective {z : Configuration}
    (hm : ∀ w : Configuration, energy w=8 → delta w ≤ delta z) : Function.Injective z := by
  intro i j he
  by_contra hne
  have hp := maximum_delta_pos hm
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · have h0 := collision_delta_zero z i j hlt he
    linarith
  · have h0 := collision_delta_zero z j i hgt he.symm
    linarith

end MordellEight
