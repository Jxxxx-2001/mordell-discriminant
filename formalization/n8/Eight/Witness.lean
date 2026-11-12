import Eight.Invariance
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Algebra.Polynomial.Derivative

namespace MordellEight
open Polynomial Finset
set_option maxHeartbeats 0

noncomputable def heptagonRoot : ℂ := Complex.exp (2*Real.pi*Complex.I/7)
noncomputable def unitHeptagon : Configuration := Fin.cases 0 (fun k : Fin 7 => heptagonRoot^k.val)

theorem heptagonRoot_primitive : IsPrimitiveRoot heptagonRoot 7 :=
  Complex.isPrimitiveRoot_exp 7 (by decide)

theorem heptagonRoot_seventh : heptagonRoot^7=1 := heptagonRoot_primitive.pow_eq_one

theorem heptagonRoot_norm : ‖heptagonRoot‖=1 := by
  unfold heptagonRoot
  have he : 2*(Real.pi : ℂ)*Complex.I/7 = ((2*Real.pi/7 : ℝ) : ℂ)*Complex.I := by
    push_cast
    ring
  rw [he,Complex.norm_exp_ofReal_mul_I]

theorem unitHeptagon_energy : energy unitHeptagon=7 := by
  rw [energy_eq_norm,Fin.sum_univ_succ]
  simp [unitHeptagon,norm_pow,heptagonRoot_norm]

noncomputable def pointPolynomial (z : Configuration) : Polynomial ℂ :=
  ∏ i, (X-C (z i))

theorem pointPolynomial_derivative_eval (z : Configuration) (i : Fin 8) :
    (pointPolynomial z).derivative.eval (z i) = ∏ j ∈ univ.erase i, (z i-z j) := by
  have hf : pointPolynomial z=(X-C (z i))*∏ j ∈ univ.erase i,(X-C (z j)) :=
    (Finset.mul_prod_erase _ _ (mem_univ i)).symm
  rw [hf]
  simp [Polynomial.eval_prod]

theorem derivative_norm_product (z : Configuration) :
    (∏ i, ‖(pointPolynomial z).derivative.eval (z i)‖^2) = (delta z)^2 := by
  rw [←offDiagProduct_eq]
  unfold offDiagProduct
  apply Finset.prod_congr rfl
  intro i hi
  rw [pointPolynomial_derivative_eval,Complex.norm_prod,←Finset.prod_pow]
  rw [←Finset.prod_erase_mul (f := fun j : Fin 8 => if i=j then (1:ℝ) else ‖z i-z j‖^2)
    _ (mem_univ i)]
  simp only [ite_true,mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  rw [if_neg (Finset.ne_of_mem_erase hj).symm]

theorem unitHeptagon_polynomial : pointPolynomial unitHeptagon=X^8-X := by
  have hp := X_pow_sub_C_eq_prod heptagonRoot_primitive
    (by norm_num : 0<7) (show (1:ℂ)^7=1 by simp)
  simp only [mul_one,C_1] at hp
  rw [Finset.prod_range] at hp
  unfold pointPolynomial
  rw [Fin.prod_univ_succ]
  simp only [unitHeptagon,Fin.cases_zero,Fin.cases_succ,map_zero,sub_zero]
  rw [←hp]
  ring

theorem unitHeptagon_derivative_zero :
    (pointPolynomial unitHeptagon).derivative.eval (unitHeptagon 0)= -1 := by
  rw [unitHeptagon_polynomial]
  norm_num [unitHeptagon,derivative_sub,derivative_pow]

theorem unitHeptagon_derivative_succ (k : Fin 7) :
    (pointPolynomial unitHeptagon).derivative.eval (unitHeptagon k.succ)=7 := by
  have hp : (heptagonRoot^k.val)^7=1 := by
    rw [←pow_mul,Nat.mul_comm,pow_mul,heptagonRoot_seventh,one_pow]
  rw [unitHeptagon_polynomial]
  norm_num [unitHeptagon,derivative_sub,derivative_pow,hp]

theorem unitHeptagon_delta : delta unitHeptagon=(7:ℝ)^7 := by
  apply (sq_eq_sq₀ (delta_nonneg _) (by positivity : (0:ℝ)≤7^7)).mp
  rw [←derivative_norm_product,Fin.prod_univ_succ,unitHeptagon_derivative_zero]
  simp_rw [unitHeptagon_derivative_succ]
  norm_num

theorem rotation_exp_heptagonRoot (θ : ℝ) (k : Fin 7) :
    Complex.exp ((θ : ℂ)*Complex.I)*heptagonRoot^k.val =
      Complex.exp (((θ+2*Real.pi*(k.val : ℝ)/7 : ℝ) : ℂ)*Complex.I) := by
  calc
    _ = Complex.exp ((θ : ℂ)*Complex.I)*
        Complex.exp ((k.val : ℂ)*(2*Real.pi*Complex.I/7)) := by
      rw [Complex.exp_nat_mul]
      rfl
    _ = _ := by
      rw [←Complex.exp_add]
      congr 1
      push_cast
      ring

theorem heptagonConfig_eq (θ : ℝ) : heptagonConfig θ =
    complexScale (Complex.exp ((θ : ℂ)*Complex.I)) (scale (Real.sqrt (8/7)) unitHeptagon) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [heptagonConfig,complexScale,scale,unitHeptagon]
  · simp only [heptagonConfig,complexScale,scale,unitHeptagon,Fin.cases_succ]
    rw [←rotation_exp_heptagonRoot]
    ring

theorem heptagonConfig_energy (θ : ℝ) : energy (heptagonConfig θ)=8 := by
  rw [heptagonConfig_eq,energy_rotate,scale_energy,unitHeptagon_energy,
    Real.sq_sqrt (by norm_num)]
  norm_num

theorem heptagonConfig_delta (θ : ℝ) : delta (heptagonConfig θ)=sharpConstant := by
  rw [heptagonConfig_eq,delta_rotate,scale_delta,unitHeptagon_delta]
  have hs : Real.sqrt (8/7 : ℝ)^2=8/7 := Real.sq_sqrt (by norm_num)
  rw [show (56:ℕ)=2*28 by norm_num,pow_mul,hs]
  norm_num [sharpConstant]

theorem witness_8 : WitnessStatement :=
  ⟨heptagonConfig_energy 0,heptagonConfig_delta 0⟩

theorem centerHeptagon_attains {z : Configuration} (hz : CenterHeptagon z) :
    energy z=8 ∧ delta z=sharpConstant := by
  obtain ⟨θ,σ,h⟩ := hz
  have he : relabel z σ=heptagonConfig θ := funext h
  constructor
  · rw [←energy_relabel z σ,he]
    exact heptagonConfig_energy θ
  · rw [←delta_relabel z σ,he]
    exact heptagonConfig_delta θ

end MordellEight
