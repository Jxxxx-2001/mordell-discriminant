import Eight.Algebraic

namespace MordellEight

def KernelCoeff.scale (a : ℚ) (c : KernelCoeff) : KernelCoeff := fun i j => a*c i j

theorem KernelCoeff.real_zero : KernelCoeff.real 0=0 := by
  simp [KernelCoeff.real,AlgebraicCoeff.real]

theorem KernelCoeff.real_add (c d : KernelCoeff) : (c+d).real=c.real+d.real := by
  simp [KernelCoeff.real,AlgebraicCoeff.real,Fin.sum_univ_succ,add_mul]
  ring

theorem KernelCoeff.real_scale (a : ℚ) (c : KernelCoeff) :
    (c.scale a).real=(a : ℝ)*c.real := by
  simp [KernelCoeff.real,AlgebraicCoeff.real,KernelCoeff.scale,Fin.sum_univ_succ]
  ring

end MordellEight
