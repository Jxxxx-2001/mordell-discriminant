import Eight.ExactKernel
import Mathlib.Analysis.Convex.Deriv

namespace MordellEight
set_option maxHeartbeats 0

theorem KernelTerm.hasDerivAt_path (p : KernelTerm) (u v t : ℝ → ℝ)
    (a b c s : ℝ) (hu : HasDerivAt u a s) (hv : HasDerivAt v b s) (ht : HasDerivAt t c s) :
    HasDerivAt (fun z => p.real (u z) (v z) (t z))
      (p.du.real (u s) (v s) (t s)*a+p.dv.real (u s) (v s) (t s)*b+
        p.dt.real (u s) (v s) (t s)*c) s := by
  have h := (((hu.pow p.u).const_mul p.coeff.real).mul (hv.pow p.v)).mul (ht.pow p.t)
  convert h using 1
  simp only [KernelTerm.real,KernelTerm.du,KernelTerm.dv,KernelTerm.dt,
    KernelCoeff.real_scale,Rat.cast_natCast,Pi.mul_apply,Pi.pow_apply]
  ring

theorem ExactKernel.hasDerivAt_path (p : ExactKernel) (u v t : ℝ → ℝ)
    (a b c s : ℝ) (hu : HasDerivAt u a s) (hv : HasDerivAt v b s) (ht : HasDerivAt t c s) :
    HasDerivAt (fun z => p.real (u z) (v z) (t z))
      (p.du.real (u s) (v s) (t s)*a+p.dv.real (u s) (v s) (t s)*b+
        p.dt.real (u s) (v s) (t s)*c) s := by
  induction p with
  | nil => simpa [ExactKernel.real,ExactKernel.du,ExactKernel.dv,ExactKernel.dt] using hasDerivAt_const s (0 : ℝ)
  | cons p ps ih =>
    have h := (p.hasDerivAt_path u v t a b c s hu hv ht).add ih
    convert h using 1
    simp only [ExactKernel.real,ExactKernel.du,ExactKernel.dv,ExactKernel.dt,List.map_cons]
    ring

theorem KernelTerm.contDiff (p : KernelTerm) :
    ContDiff ℝ ⊤ (fun x : Fin 3 → ℝ => p.real (x 0) (x 1) (x 2)) := by
  unfold KernelTerm.real
  fun_prop

theorem ExactKernel.contDiff (p : ExactKernel) :
    ContDiff ℝ ⊤ (fun x : Fin 3 → ℝ => p.real (x 0) (x 1) (x 2)) := by
  induction p with
  | nil => exact contDiff_const
  | cons p ps ih => exact p.contDiff.add ih

end MordellEight
