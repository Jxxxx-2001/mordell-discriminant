import N7.Kernel.Local.Parameters
set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 0
namespace N7.Kernel.Local.C0
open GapAnalytic LocalGeometry
theorem value_checked : exactMajorant.atRat 0 1 0=⟨0,0,0⟩ := by decide +kernel
theorem derivative1_checked : exactMajorant.dv.atRat 0 1 0=⟨1,0,0⟩ := by decide +kernel
theorem derivative2_checked : exactMajorant.dt.atRat 0 1 0=⟨-2,0,0⟩ := by decide +kernel
theorem contact_value : gap exactMajorant (point center)=0 := by
  have h := congrArg KernelCoeff.real value_checked
  rw [ExactKernel.real_atRat] at h
  norm_num [gap,eval3,point,center,distance,KernelCoeff.real,Matrix.cons_val_two] at h ⊢
  linarith
theorem contact_gradient1 : gradient exactMajorant (point center) 1=0 := by
  have h := congrArg KernelCoeff.real derivative1_checked
  rw [ExactKernel.real_atRat] at h
  norm_num [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,gradient,partialPoly,eval3,point,center,distance,dd,KernelCoeff.real,Matrix.cons_val_two] at h ⊢
  linarith
theorem contact_gradient2 : gradient exactMajorant (point center) 2=0 := by
  have h := congrArg KernelCoeff.real derivative2_checked
  rw [ExactKernel.real_atRat] at h
  norm_num [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,gradient,partialPoly,eval3,point,center,distance,dd,KernelCoeff.real,Matrix.cons_val_two] at h ⊢
  linarith
#print axioms contact_value
end N7.Kernel.Local.C0
