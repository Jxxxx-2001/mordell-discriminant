import Eight.ExactKernel
import Eight.AlgebraicArithmetic

namespace MordellEight

def KernelTerm.atAlgebraic (s : KernelTerm) (u v t : AlgebraicCoeff) : KernelCoeff :=
  s.coeff.mulAlgebraic (((u.power s.u).mul (v.power s.v)).mul (t.power s.t))

theorem KernelTerm.atAlgebraic_real (s : KernelTerm) (u v t : AlgebraicCoeff) :
    (s.atAlgebraic u v t).real=s.real u.real v.real t.real := by
  simp only [atAlgebraic,KernelCoeff.mulAlgebraic_real,AlgebraicCoeff.mul_real,
    AlgebraicCoeff.power_real,KernelTerm.real]
  ring

def ExactKernel.atAlgebraic : ExactKernel → AlgebraicCoeff → AlgebraicCoeff → AlgebraicCoeff → KernelCoeff
  | [],_,_,_ => 0
  | s::ss,u,v,t => s.atAlgebraic u v t+ExactKernel.atAlgebraic ss u v t

theorem ExactKernel.atAlgebraic_real (p : ExactKernel) (u v t : AlgebraicCoeff) :
    (p.atAlgebraic u v t).real=p.real u.real v.real t.real := by
  induction p with
  | nil => simp [atAlgebraic,real,KernelCoeff.real_zero]
  | cons s ss ih =>
    simp only [atAlgebraic,real,KernelCoeff.real_add,KernelTerm.atAlgebraic_real,ih]

end MordellEight
