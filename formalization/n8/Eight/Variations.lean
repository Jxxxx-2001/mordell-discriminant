import Eight.Centering
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace MordellEight
open Filter Set
open scoped Topology
set_option maxHeartbeats 0

/-- The real Euclidean pairing, independent of the sup norm on the function type. -/
def realDot (a b : ℂ) : ℝ := a.re*b.re+a.im*b.im

def affine (z w : Configuration) (s : ℝ) : Configuration := fun i => z i+(s : ℂ)*w i

theorem affine_zero (z w : Configuration) : affine z w 0=z := by ext i; simp [affine]

theorem realDot_self (a : ℂ) : realDot a a=‖a‖^2 := by
  rw [norm_sq_coordinates]
  dsimp [realDot]
  ring

theorem norm_affine_complex (a b : ℂ) (s : ℝ) :
    ‖a+(s : ℂ)*b‖^2=‖a‖^2+2*s*realDot a b+s^2*‖b‖^2 := by
  simp only [norm_sq_coordinates,realDot,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem realDot_affine_complex (a b : ℂ) (s : ℝ) :
    realDot (a+(s : ℂ)*b) b=realDot a b+s*‖b‖^2 := by
  simp only [realDot,norm_sq_coordinates,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem norm_affine_hasDerivAt (a b : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ‖a+(t : ℂ)*b‖^2)
      (2*realDot (a+(s : ℂ)*b) b) s := by
  simp_rw [norm_affine_complex]
  have h := (((hasDerivAt_id s).const_mul (2*realDot a b)).add_const (‖a‖^2)).add
    (((hasDerivAt_id s).pow 2).mul_const (‖b‖^2))
  convert h using 1
  · funext t
    dsimp
    ring
  · simp [realDot_affine_complex] <;> ring

theorem realDot_affine_hasDerivAt (a b : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => realDot (a+(t : ℂ)*b) b) (‖b‖^2) s := by
  simp_rw [realDot_affine_complex]
  simpa using ((hasDerivAt_id s).mul_const (‖b‖^2)).const_add (realDot a b)

theorem realDot_div_norm_sq (a b : ℂ) : realDot a b/‖a‖^2=(b/a).re := by
  rw [Complex.div_re,norm_sq_coordinates]
  simp only [Complex.normSq_apply,realDot]
  ring

theorem norm_ratio_identity (a b : ℂ) (ha : a≠0) :
    ‖b‖^2/‖a‖^2-2*(realDot a b/‖a‖^2)^2 = -((b/a)^2).re := by
  have hnorm : a.re^2+a.im^2≠0 := by
    rw [←norm_sq_coordinates]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  rw [norm_sq_coordinates,norm_sq_coordinates]
  simp only [realDot,pow_two,Complex.mul_re,
    Complex.div_re,Complex.div_im,Complex.normSq_apply]
  field_simp [hnorm]
  ring

noncomputable def logLineFirst (a b : ℂ) (s : ℝ) : ℝ :=
  2*realDot (a+(s : ℂ)*b) b/‖a+(s : ℂ)*b‖^2

theorem log_norm_affine_hasDerivAt (a b : ℂ) (s : ℝ) (ha : a+(s : ℂ)*b≠0) :
    HasDerivAt (fun t : ℝ => Real.log (‖a+(t : ℂ)*b‖^2)) (logLineFirst a b s) s :=
  (norm_affine_hasDerivAt a b s).log (pow_ne_zero _ (norm_ne_zero_iff.mpr ha))

theorem logLineFirst_hasDerivAt (a b : ℂ) (s : ℝ) (ha : a+(s : ℂ)*b≠0) :
    HasDerivAt (logLineFirst a b) (-2*((b/(a+(s : ℂ)*b))^2).re) s := by
  have hn : ‖a+(s : ℂ)*b‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have h := ((realDot_affine_hasDerivAt a b s).const_mul 2).div
    (norm_affine_hasDerivAt a b s) hn
  convert h using 1
  have hi := norm_ratio_identity (a+(s : ℂ)*b) b ha
  field_simp [hn] at hi ⊢
  nlinarith [hi]

/-- Necessary second derivative condition; zero second derivatives are allowed. -/
theorem localMax_second_nonpos {f : ℝ → ℝ} {a : ℝ}
    (hm : IsLocalMax f a) (hc : ContinuousAt f a) : deriv (deriv f) a≤0 := by
  by_contra h
  have hp : 0<deriv (deriv f) a := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hm,hmin] with x hx hy
    exact le_antisymm hx hy
  have hz := he.deriv.deriv_eq
  have hc' : deriv (fun _ : ℝ => f a) = (fun _ : ℝ => 0) := by
    funext x
    exact deriv_const x (f a)
  rw [hc',deriv_const] at hz
  linarith

end MordellEight
