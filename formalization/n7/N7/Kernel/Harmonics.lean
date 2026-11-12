-- Adapted from the verified Eight/KernelHarmonics.lean; independent of point count.
import N7.Statement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
namespace N7.Kernel
open Matrix Finset
set_option maxHeartbeats 0

theorem quadratic_expand {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (A*ᵥx)=∑ i,∑ j,x i*A i j*x j := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

def harmonic : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _, _, _ => 1
  | 1, _, _, t => t
  | k+2, u, v, t => 2*t*harmonic (k+1) u v t-u*v*harmonic k u v t

theorem complex_power_recurrence (c : ℂ) (k : ℕ) :
    (c^(k+2)).re=2*c.re*(c^(k+1)).re-‖c‖^2*(c^k).re := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_add,pow_two,pow_one,Complex.mul_re,Complex.mul_im]
  ring

theorem harmonic_actual (a b : ℂ) (k : ℕ) :
    harmonic k (‖a‖^2) (‖b‖^2) (a*star b).re=((a*star b)^k).re := by
  induction k using Nat.twoStepInduction with
  | zero => simp [harmonic]
  | one => simp [harmonic]
  | more k ih ih' =>
    rw [harmonic,ih',ih]
    have h := complex_power_recurrence (a*star b) k
    simpa only [norm_mul,norm_star,mul_pow] using h.symm

noncomputable def complexQuadratic {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (S : Fin n → ℂ) : ℝ :=
  ∑ a,∑ b,Q a b*(S a*star (S b)).re

theorem complexQuadratic_split {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (S : Fin n → ℂ) :
    complexQuadratic Q S=(fun a => (S a).re) ⬝ᵥ (Q*ᵥ(fun a => (S a).re))+
      (fun a => (S a).im) ⬝ᵥ (Q*ᵥ(fun a => (S a).im)) := by
  rw [quadratic_expand,quadratic_expand]
  unfold complexQuadratic
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem complexQuadratic_nonneg {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosSemidef) (S : Fin n → ℂ) : 0≤complexQuadratic Q S := by
  rw [complexQuadratic_split]
  exact add_nonneg (by simpa only [star_trivial] using hQ.dotProduct_mulVec_nonneg (fun a => (S a).re))
    (by simpa only [star_trivial] using hQ.dotProduct_mulVec_nonneg (fun a => (S a).im))

theorem complexQuadratic_zero_iff {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosDef) (S : Fin n → ℂ) : complexQuadratic Q S=0 ↔ S=0 := by
  constructor
  · intro h
    rw [complexQuadratic_split] at h
    have hr : 0≤(fun a => (S a).re) ⬝ᵥ (Q*ᵥ(fun a => (S a).re)) := by
      simpa only [star_trivial] using hQ.posSemidef.dotProduct_mulVec_nonneg (fun a => (S a).re)
    have hi : 0≤(fun a => (S a).im) ⬝ᵥ (Q*ᵥ(fun a => (S a).im)) := by
      simpa only [star_trivial] using hQ.posSemidef.dotProduct_mulVec_nonneg (fun a => (S a).im)
    have hre : (fun a => (S a).re)=0 := by
      by_contra hn
      have hp := hQ.dotProduct_mulVec_pos hn
      simp only [star_trivial] at hp
      linarith
    have him : (fun a => (S a).im)=0 := by
      by_contra hn
      have hp := hQ.dotProduct_mulVec_pos hn
      simp only [star_trivial] at hp
      linarith
    funext a
    apply Complex.ext
    · exact congrFun hre a
    · exact congrFun him a
  · rintro rfl
    simp [complexQuadratic]

theorem double_sum_separable_re {m : ℕ} (f g : Fin m → ℂ) :
    (∑ i,∑ j,(f i*star (g j)).re)=((∑ i,f i)*star (∑ j,g j)).re := by
  simp only [star_sum,Finset.mul_sum,Finset.sum_mul,Complex.re_sum]
  exact Finset.sum_comm

theorem weighted_harmonic_term (a b : ℂ) (k : ℕ) (f g : ℝ) :
    harmonic k (‖a‖^2) (‖b‖^2) (a*star b).re*f*g=
      (a^k*(f : ℂ)*star (b^k*(g : ℂ))).re := by
  rw [harmonic_actual]
  simp only [mul_pow,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im]
  ring

theorem weighted_harmonic_sum {m : ℕ} (z : Fin m → ℂ) (k : ℕ) (f g : Fin m → ℝ) :
    (∑ i,∑ j,harmonic k (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re*f i*g j)=
      ((∑ i,(z i)^k*(f i : ℂ))*star (∑ j,(z j)^k*(g j : ℂ))).re := by
  simp_rw [weighted_harmonic_term]
  exact double_sum_separable_re _ _

end N7.Kernel
