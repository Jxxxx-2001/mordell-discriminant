import N7.Kernel.Local.Parameters
set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 0
namespace N7.Kernel.Local.C3
open GapAnalytic LocalGeometry
attribute [local irreducible] boundaryPolynomial
theorem value_checked : boundaryPolynomial.atRat 1 1 (-1)=⟨0,2,0⟩ := by decide +kernel
theorem derivative0_checked : boundaryPolynomial.du.atRat 1 1 (-1)=⟨(1/4:ℚ),0,0⟩ := by decide +kernel
theorem derivative1_checked : boundaryPolynomial.dv.atRat 1 1 (-1)=⟨(1/4:ℚ),0,0⟩ := by decide +kernel
theorem derivative2_checked : boundaryPolynomial.dt.atRat 1 1 (-1)=⟨(-1/2:ℚ),0,0⟩ := by decide +kernel
theorem contact_value : gap boundaryPolynomial (point center)=0 := by
  have h := congrArg KernelCoeff.real value_checked
  rw [ExactKernel.real_atRat] at h
  have hl : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  norm_num [gap,eval3,point,center,distance,KernelCoeff.real,Matrix.cons_val_two,hl] at h ⊢
  linarith
theorem contact_gradient0 : gradient boundaryPolynomial (point center) 0=0 := by
  have h := congrArg KernelCoeff.real derivative0_checked
  rw [ExactKernel.real_atRat] at h
  norm_num [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,gradient,partialPoly,eval3,point,center,distance,dd,KernelCoeff.real,Matrix.cons_val_two] at h ⊢
  linarith
theorem contact_gradient1 : gradient boundaryPolynomial (point center) 1=0 := by
  have h := congrArg KernelCoeff.real derivative1_checked
  rw [ExactKernel.real_atRat] at h
  norm_num [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,gradient,partialPoly,eval3,point,center,distance,dd,KernelCoeff.real,Matrix.cons_val_two] at h ⊢
  linarith
theorem contact_gradient2 : gradient boundaryPolynomial (point center) 2=0 := by
  have h := congrArg KernelCoeff.real derivative2_checked
  rw [ExactKernel.real_atRat] at h
  norm_num [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,gradient,partialPoly,eval3,point,center,distance,dd,KernelCoeff.real,Matrix.cons_val_two] at h ⊢
  linarith
theorem contact_gradient (i : Fin 3) : gradient boundaryPolynomial (point center) i=0 := by
  fin_cases i
  · exact contact_gradient0
  · exact contact_gradient1
  · exact contact_gradient2
#print axioms contact_value
end N7.Kernel.Local.C3
