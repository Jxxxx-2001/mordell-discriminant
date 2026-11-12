import N7.Kernel.LocalGeometry
set_option autoImplicit false
namespace N7.Kernel.LocalInward
open GapAnalytic

def distanceTimes : ExactKernel → ExactKernel
  | [] => []
  | s::p => ⟨s.u+1,s.v,s.t,s.coeff⟩ :: ⟨s.u,s.v+1,s.t,s.coeff⟩ ::
    ⟨s.u,s.v,s.t+1,s.coeff.scale (-2)⟩ :: distanceTimes p

theorem distanceTimes_real (p : ExactKernel) (u v t : ℝ) :
    (distanceTimes p).real u v t=(u+v-2*t)*p.real u v t := by
  induction p with
  | nil => simp [distanceTimes,ExactKernel.real]
  | cons s p ih =>
    simp only [distanceTimes,ExactKernel.real,KernelTerm.real,KernelCoeff.real_scale,ih,pow_succ]
    norm_num
    ring

def inwardPolynomial (p : ExactKernel) : ExactKernel :=
  distanceTimes p.du ++ [⟨0,0,0,⟨-1,0,0⟩⟩]

theorem inwardPolynomial_real (p : ExactKernel) (x : Fin 3 → ℝ) :
    eval3 (inwardPolynomial p) x=distance x*eval3 p.du x-1 := by
  rw [inwardPolynomial,eval3_append]
  simp only [eval3,distanceTimes_real,distance,ExactKernel.real,KernelTerm.real,KernelCoeff.real,pow_zero]
  norm_num
  ring

end N7.Kernel.LocalInward
