import Eight.Q6

namespace MordellEight

/-- Ascending coefficient coordinates of the source's descending lists for entry [6,0,0]. -/
def q6Encoded00 : KernelCoeff :=
  ![![-6576334255/15465909004,0,0],
    ![15/98,-4/49,0], ![23/98,0,-8/49], ![11/98,4/49,8/49]]

theorem q6Encoded00_real : q6Encoded00.real = q6Entry00 := by
  norm_num [KernelCoeff.real,AlgebraicCoeff.real,q6Encoded00,q6Entry00,
    Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  ring

def rationalKernelCoeff (q : ℚ) : KernelCoeff := ![![q,0,0],0,0,0]
theorem rationalKernelCoeff_real (q : ℚ) : (rationalKernelCoeff q).real = (q : ℝ) := by
  norm_num [rationalKernelCoeff,KernelCoeff.real,AlgebraicCoeff.real,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

def q6Coefficients (i j : Fin 4) : KernelCoeff :=
  if i=0 ∧ j=0 then q6Encoded00 else rationalKernelCoeff (q6Lower i j)

theorem Q6_coefficient_semantics (i j : Fin 4) : Q6 i j = (q6Coefficients i j).real := by
  by_cases h : i=0 ∧ j=0
  · simp only [Q6,q6Coefficients,if_pos h,q6Encoded00_real]
  · simp only [Q6,q6Coefficients,if_neg h,rationalKernelCoeff_real]

end MordellEight
