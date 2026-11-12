import Chalk.Integer
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Analysis.Complex.Polynomial.Basic

open Finset Polynomial
namespace Chalk

noncomputable def energy {n : ℕ} (z : Fin n → ℂ) : ℝ := ∑ i, ‖z i‖^2
/-- Each unordered pair occurs once. -/
noncomputable def delta {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i, ∏ j, if i < j then ‖z i-z j‖^2 else 1

theorem delta_cons {n : ℕ} (a : ℂ) (z : Fin n → ℂ) :
    delta (Fin.cases a z) = (∏ j, ‖a-z j‖^2) * delta z := by
  unfold delta
  rw [Fin.prod_univ_succ]
  simp [Fin.prod_univ_succ]

theorem delta_scale {n : ℕ} (c : ℂ) (z : Fin n → ℂ) :
    delta (fun i => c*z i) = (‖c‖^2)^(n.choose 2) * delta z := by
  induction n with
  | zero => simp [delta]
  | succ n ih =>
    let w := fun i : Fin n => z i.succ
    have hz : z = Fin.cases (z 0) w := funext (Fin.cases rfl (fun _ => rfl))
    have hc : (fun i => c*z i) = Fin.cases (c*z 0) (fun i => c*w i) :=
      funext (Fin.cases rfl (fun _ => rfl))
    rw [hc, delta_cons, ih, show delta z = _ from congrArg delta hz, delta_cons]
    simp_rw [←mul_sub, norm_mul, mul_pow]
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, Nat.choose_succ_succ,
      Nat.choose_one_right, pow_add]
    ring

theorem energy_scale {n : ℕ} (c : ℂ) (z : Fin n → ℂ) :
    energy (fun i => c*z i) = ‖c‖^2 * energy z := by
  simp [energy,mul_pow,mul_sum]

private theorem derivative_product {n : ℕ} (z : Fin n → ℂ) :
    (∏ i, ‖(∏ j, (X - C (z j))).derivative.eval (z i)‖) = delta z := by
  let g := fun i j : Fin n => if i<j then ‖z i-z j‖ else 1
  have row (i : Fin n) :
      ‖(∏ j, (X-C (z j))).derivative.eval (z i)‖ = ∏ j, (g i j*g j i) := by
    rw [←mul_prod_erase univ (fun j => X-C (z j)) (mem_univ i)]
    simp only [derivative_mul,derivative_sub,derivative_X,derivative_C,sub_zero,one_mul,
      eval_add,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul,add_zero,eval_prod,
      Complex.norm_prod]
    rw [←mul_prod_erase univ (fun j => g i j*g j i) (mem_univ i)]
    simp only [g,lt_irrefl,if_false,one_mul]
    apply prod_congr rfl
    intro j hj
    rcases lt_or_gt_of_ne (ne_of_mem_erase hj).symm with h|h
    · simp [h,not_lt.mpr h.le]
    · simp [h,not_lt.mpr h.le,norm_sub_rev (z j) (z i)]
  simp_rw [row,prod_mul_distrib]
  rw [prod_comm (f := fun i j => g j i)]
  unfold delta
  rw [←prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [←prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  by_cases h : i<j <;> simp [g,h,sq]

theorem unit_ring_delta {p : ℕ} (hp : 0<p) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) :
    delta (fun j : Fin p => ζ^j.val) = (p:ℝ)^p := by
  have hpoly := X_pow_sub_C_eq_prod hζ hp (α := (1:ℂ)) (one_pow p)
  simp only [mul_one, C_1] at hpoly
  rw [prod_range] at hpoly
  rw [← derivative_product, ←hpoly]
  simp [derivative_sub,derivative_pow, hζ.norm'_eq_one hp.ne', norm_pow]

/-- Product of all squared distances from a real point to the rotated outer ring. -/
theorem cross_product {p : ℕ} (hp : 0<p) {ζ α : ℂ} (hζ : IsPrimitiveRoot ζ p)
    (R a : ℝ) (hα : α^p = Complex.I*(R:ℂ)^p) :
    (a^p)^2 + (R^2)^p = ∏ j : Fin p, ‖(a:ℂ)-ζ^j.val*α‖^2 := by
  have h := X_pow_sub_C_eq_prod hζ hp hα
  rw [prod_range] at h
  have he := congrArg (fun q : ℂ[X] => q.eval (a:ℂ)) h
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod] at he
  rw [prod_pow, ←Complex.norm_prod, ←he, Complex.sq_norm, Complex.normSq_apply]
  simp only [←Complex.ofReal_pow, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [show (R^2)^p = (R^p)^2 by rw [←pow_mul, Nat.mul_comm 2 p, pow_mul]]
  ring

end Chalk
