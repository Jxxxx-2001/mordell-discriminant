import Eight.CoefficientArithmetic

namespace MordellEight

def AlgebraicCoeff.one : AlgebraicCoeff := ![1,0,0]
def AlgebraicCoeff.mul (a b : AlgebraicCoeff) : AlgebraicCoeff :=
  ![a 0*b 0+(a 1*b 2+a 2*b 1)/8-a 2*b 2/16,
    a 0*b 1+a 1*b 0+(a 1*b 2+a 2*b 1)/2-a 2*b 2/8,
    a 0*b 2+a 1*b 1+a 2*b 0-(a 1*b 2+a 2*b 1)/2+3*a 2*b 2/4]

theorem AlgebraicCoeff.one_real : AlgebraicCoeff.one.real=1 := by
  norm_num [AlgebraicCoeff.one,AlgebraicCoeff.real,Matrix.cons_val_two]

theorem AlgebraicCoeff.mul_real (a b : AlgebraicCoeff) :
    (a.mul b).real=a.real*b.real := by
  have h := alpha_equation
  unfold cubic at h
  norm_num [AlgebraicCoeff.mul,AlgebraicCoeff.real,Matrix.cons_val_two,
    Matrix.vecHead,Matrix.vecTail]
  linear_combination
    -(((a 1:ℝ)*(b 2:ℝ)+(a 2:ℝ)*(b 1:ℝ))+(alpha-1/2)*(a 2:ℝ)*(b 2:ℝ))/8*h

def AlgebraicCoeff.power (a : AlgebraicCoeff) : ℕ → AlgebraicCoeff
  | 0 => AlgebraicCoeff.one
  | n+1 => (a.power n).mul a

theorem AlgebraicCoeff.power_real (a : AlgebraicCoeff) (n : ℕ) :
    (a.power n).real=a.real^n := by
  induction n with
  | zero => simp [power,one_real]
  | succ n ih => rw [power,mul_real,ih,pow_succ]

def KernelCoeff.mulAlgebraic (a : AlgebraicCoeff) (c : KernelCoeff) : KernelCoeff :=
  fun j => (c j).mul a

theorem KernelCoeff.mulAlgebraic_real (a : AlgebraicCoeff) (c : KernelCoeff) :
    (c.mulAlgebraic a).real=c.real*a.real := by
  simp only [KernelCoeff.real,KernelCoeff.mulAlgebraic,AlgebraicCoeff.mul_real,
    add_mul,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

end MordellEight
