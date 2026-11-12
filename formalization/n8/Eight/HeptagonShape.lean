import Eight.Newton
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace MordellEight
open Finset
set_option maxHeartbeats 0

noncomputable def unitHeptagonOrbit (a : ℂ) : Configuration :=
  Fin.cases 0 (fun k : Fin 7 => a*heptagonRoot^k.val)

noncomputable def UnitHeptagonShape (z : Configuration) : Prop :=
  ∃ a : ℂ,‖a‖=1 ∧ ∃ σ : Equiv.Perm (Fin 8),z (σ 0)=0 ∧
    ∀ k : Fin 7,z (σ k.succ)=a*heptagonRoot^k.val

/-- A finite pointwise cover plus injectivity gives an actual permutation, not just set membership. -/
theorem relabel_of_cover (z c : Configuration) (hz : Function.Injective z)
    (hc : ∀ i,∃ j,z i=c j) : ∃ σ : Equiv.Perm (Fin 8),∀ i,z (σ i)=c i := by
  choose f hf using hc
  have hi : Function.Injective f := by
    intro i j hij
    apply hz
    rw [hf i,hf j,hij]
  let e : Equiv.Perm (Fin 8) := Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩
  refine ⟨e.symm,fun i => ?_⟩
  rw [hf]
  exact congrArg c (e.apply_symm_apply i)

theorem binary_power_sums_shape (z : Configuration) (hE : energy z=7)
    (hi : Function.Injective z) (hr : ∀ i,‖z i‖^2=0 ∨ ‖z i‖^2=1)
    (hp : ∀ k : ℕ,0<k → k<7 → (∑ i,(z i)^k)=0) : UnitHeptagonShape z := by
  obtain ⟨origin,horigin⟩ := radius_binary_origin hE hr
  obtain ⟨anchor,hanchor⟩ : ∃ j,z j≠0 := by
    by_contra hn
    push Not at hn
    have he : energy z=0 := by simp [energy_eq_norm,hn]
    linarith
  have ha2 : ‖z anchor‖^2=1 :=
    (hr anchor).resolve_left (pow_ne_zero _ (norm_ne_zero_iff.mpr hanchor))
  have ha : ‖z anchor‖=1 := by nlinarith [norm_nonneg (z anchor)]
  have hpowA := nonzero_seventh_power_common z hp ⟨origin,horigin⟩ anchor hanchor
  have hconstant : (pointMultiset z).esymm 7≠0 := by
    rw [←hpowA]
    exact pow_ne_zero _ hanchor
  have hcover (i : Fin 8) : ∃ j,z i=unitHeptagonOrbit (z anchor) j := by
    by_cases hzero : z i=0
    · exact ⟨0,hzero⟩
    · have hpow := nonzero_seventh_power_common z hp ⟨origin,horigin⟩ i hzero
      have hratio : (z i/z anchor)^7=1 := by
        rw [div_pow,hpow,hpowA,div_self hconstant]
      obtain ⟨k,hk,hval⟩ := heptagonRoot_primitive.eq_pow_of_pow_eq_one hratio
      refine ⟨(⟨k,hk⟩ : Fin 7).succ,?_⟩
      change z i=z anchor*heptagonRoot^k
      rw [hval]
      field_simp
  obtain ⟨σ,hσ⟩ := relabel_of_cover z (unitHeptagonOrbit (z anchor)) hi hcover
  exact ⟨z anchor,ha,σ,hσ 0,fun k => hσ k.succ⟩

theorem denormalized_point (z : Configuration) (i : Fin 8) :
    z i=(Real.sqrt (8/7 : ℝ) : ℂ)*normalized z i := by
  have h : Real.sqrt (8/7 : ℝ)*Real.sqrt (7/8 : ℝ)=1 := by
    rw [←Real.sqrt_mul (by norm_num : (0 : ℝ)≤8/7)]
    norm_num
  dsimp [normalized,scale]
  rw [←mul_assoc,←Complex.ofReal_mul,h,Complex.ofReal_one,one_mul]

theorem unitOrbit_exp (a : ℂ) (ha : ‖a‖=1) (k : Fin 7) :
    a*heptagonRoot^k.val=Complex.exp
      (Complex.I*((Complex.arg a+2*Real.pi*(k.val : ℝ)/7 : ℝ) : ℂ)) := by
  have he : Complex.exp ((Complex.arg a : ℂ)*Complex.I)=a := by
    simpa only [ha,Complex.ofReal_one,one_mul] using Complex.norm_mul_exp_arg_mul_I a
  calc
    _ = Complex.exp ((Complex.arg a : ℂ)*Complex.I)*
        Complex.exp ((k.val : ℂ)*(2*Real.pi*Complex.I/7)) := by
      rw [Complex.exp_nat_mul,he]
      rfl
    _ = _ := by
      rw [←Complex.exp_add]
      congr 1
      push_cast
      ring

theorem normalized_shape_to_centerHeptagon (z : Configuration)
    (hs : UnitHeptagonShape (normalized z)) : CenterHeptagon z := by
  obtain ⟨a,ha,σ,hzero,hrest⟩ := hs
  refine ⟨Complex.arg a,σ,fun i => ?_⟩
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [denormalized_point z (σ 0),hzero,mul_zero]
    rfl
  · rw [denormalized_point z (σ k.succ),hrest,unitOrbit_exp a ha k]
    simp only [heptagonConfig,Fin.cases_succ]
    congr 2
    ring

end MordellEight
