import Eight.CoefficientArithmetic
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace MordellEight
open Finset
structure KernelTerm where
  u : ℕ
  v : ℕ
  t : ℕ
  coeff : KernelCoeff

noncomputable def KernelTerm.real (s : KernelTerm) (u v t : ℝ) : ℝ :=
  s.coeff.real*u^s.u*v^s.v*t^s.t

def KernelTerm.atRat (s : KernelTerm) (u v t : ℚ) : KernelCoeff :=
  s.coeff.scale (u^s.u*v^s.v*t^s.t)

theorem KernelTerm.real_atRat (s : KernelTerm) (u v t : ℚ) :
    (s.atRat u v t).real = s.real u v t := by
  simp [KernelTerm.atRat, KernelCoeff.real_scale, KernelTerm.real]
  ring

def KernelTerm.du (s : KernelTerm) : KernelTerm :=
  ⟨s.u-1,s.v,s.t,s.coeff.scale s.u⟩
def KernelTerm.dv (s : KernelTerm) : KernelTerm :=
  ⟨s.u,s.v-1,s.t,s.coeff.scale s.v⟩
def KernelTerm.dt (s : KernelTerm) : KernelTerm :=
  ⟨s.u,s.v,s.t-1,s.coeff.scale s.t⟩

theorem KernelTerm.hasDerivAt_u (s : KernelTerm) (u v t : ℝ) :
    HasDerivAt (fun z => s.real z v t) (s.du.real u v t) u := by
  convert (((hasDerivAt_pow s.u u).const_mul s.coeff.real).mul_const (v^s.v)).mul_const
    (t^s.t) using 1
  simp only [KernelTerm.real, KernelTerm.du, KernelCoeff.real_scale, Rat.cast_natCast]
  ring

theorem KernelTerm.hasDerivAt_v (s : KernelTerm) (u v t : ℝ) :
    HasDerivAt (fun z => s.real u z t) (s.dv.real u v t) v := by
  convert ((hasDerivAt_pow s.v v).const_mul (s.coeff.real*u^s.u)).mul_const
    (t^s.t) using 1
  simp only [KernelTerm.real, KernelTerm.dv, KernelCoeff.real_scale, Rat.cast_natCast]
  ring

theorem KernelTerm.hasDerivAt_t (s : KernelTerm) (u v t : ℝ) :
    HasDerivAt (fun z => s.real u v z) (s.dt.real u v t) t := by
  convert (hasDerivAt_pow s.t t).const_mul (s.coeff.real*u^s.u*v^s.v) using 1
  simp only [KernelTerm.real, KernelTerm.dt, KernelCoeff.real_scale, Rat.cast_natCast]
  ring

abbrev ExactKernel := List KernelTerm

noncomputable def ExactKernel.real : ExactKernel → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _ => 0
  | s::ss, u, v, t => s.real u v t+ExactKernel.real ss u v t

def ExactKernel.atRat : ExactKernel → ℚ → ℚ → ℚ → KernelCoeff
  | [], _, _, _ => 0
  | s::ss, u, v, t => s.atRat u v t+ExactKernel.atRat ss u v t

def ExactKernel.du (p : ExactKernel) : ExactKernel := p.map KernelTerm.du
def ExactKernel.dv (p : ExactKernel) : ExactKernel := p.map KernelTerm.dv
def ExactKernel.dt (p : ExactKernel) : ExactKernel := p.map KernelTerm.dt

theorem ExactKernel.real_atRat (p : ExactKernel) (u v t : ℚ) :
    (p.atRat u v t).real = p.real u v t := by
  induction p with
  | nil => simp [ExactKernel.atRat, ExactKernel.real, KernelCoeff.real_zero]
  | cons s ss ih =>
    simp only [ExactKernel.atRat, ExactKernel.real, KernelCoeff.real_add,
      KernelTerm.real_atRat, ih]

theorem ExactKernel.hasDerivAt_u (p : ExactKernel) (u v t : ℝ) :
    HasDerivAt (fun z => p.real z v t) (p.du.real u v t) u := by
  induction p with
  | nil => simpa [ExactKernel.real, ExactKernel.du] using hasDerivAt_const u (0 : ℝ)
  | cons s ss ih =>
    simpa [ExactKernel.real, ExactKernel.du] using (s.hasDerivAt_u u v t).add ih

theorem ExactKernel.hasDerivAt_v (p : ExactKernel) (u v t : ℝ) :
    HasDerivAt (fun z => p.real u z t) (p.dv.real u v t) v := by
  induction p with
  | nil => simpa [ExactKernel.real, ExactKernel.dv] using hasDerivAt_const v (0 : ℝ)
  | cons s ss ih =>
    simpa [ExactKernel.real, ExactKernel.dv] using (s.hasDerivAt_v u v t).add ih

theorem ExactKernel.hasDerivAt_t (p : ExactKernel) (u v t : ℝ) :
    HasDerivAt (fun z => p.real u v z) (p.dt.real u v t) t := by
  induction p with
  | nil => simpa [ExactKernel.real, ExactKernel.dt] using hasDerivAt_const t (0 : ℝ)
  | cons s ss ih =>
    simpa [ExactKernel.real, ExactKernel.dt] using (s.hasDerivAt_t u v t).add ih

end MordellEight
