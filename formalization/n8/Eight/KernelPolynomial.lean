import Eight.DenseProduct
import Eight.DensePadding
import Eight.ConstantIdentities

namespace MordellEight
open Matrix Finset
set_option maxHeartbeats 0
set_option maxRecDepth 30000

def featureZeroQ : Fin 4 → List ℚ :=
  ![[-7/8,1],[0,-1,1],[0,0,-1,1],[0,0,0,-1,1]]
def featureAngularQ : Fin 4 → List ℚ :=
  ![[1],[-1,1],[1,-2,1],[-1,3,-3,1]]
def featureQ (k : Fin 7) (a : Fin 4) : List ℚ := if k=0 then featureZeroQ a else featureAngularQ a

theorem featureQ_real (k : Fin 7) (a : Fin 4) (u : ℝ) :
    horner (fun c : ℚ => (c : ℝ)) (featureQ k a) u=radialFeature k u a := by
  fin_cases k <;> fin_cases a <;>
    norm_num [featureQ,featureZeroQ,featureAngularQ,radialFeature,horner,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,
      Matrix.vecTail,Function.comp_def] <;> ring <;> simp

def radialDense (k : Fin 7) : DenseKernel :=
  denseSum (List.ofFn (fun a : Fin 4 => denseSum (List.ofFn (fun b : Fin 4 =>
    ((DenseKernel.constant (allMatrixCoefficients k a b)).timesPoly 0 (featureQ k a)).timesPoly 1 (featureQ k b)))))

theorem radialDense_real (k : Fin 7) (u v t : ℝ) :
    (radialDense k).real u v t=(radialFeature k u) ⬝ᵥ (kernelQ k*ᵥradialFeature k v) := by
  simp only [radialDense,denseSum_real,List.map_ofFn,List.sum_ofFn,Function.comp_def,DenseKernel.timesPoly_real,
    DenseKernel.constant_real,axisValue,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp_rw [featureQ_real]
  simp only [kernelQ,kernelMatrixReal,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

def pieceDense (k : Fin 7) : DenseKernel := (radialDense k).angularTimes k.val

theorem pieceDense_real (k : Fin 7) (u v t : ℝ) : (pieceDense k).real u v t=kernelPiece k u v t := by
  rw [pieceDense,DenseKernel.angularTimes_real,radialDense_real]
  rfl

def kernelDenseSum (pieces : Fin 7 → DenseKernel) : DenseKernel := denseSum (List.ofFn pieces)

theorem kernelDenseSum_real (pieces : Fin 7 → DenseKernel)
    (hp : ∀ k u v t,(pieces k).real u v t=kernelPiece k u v t) (u v t : ℝ) :
    (kernelDenseSum pieces).real u v t=kernelFromMatrices u v t := by
  simp only [kernelDenseSum,denseSum_real,List.map_ofFn,List.sum_ofFn,kernelFromMatrices]
  exact Finset.sum_congr rfl (fun k _ => hp k u v t)

def majorantBaseDense : DenseKernel :=
  denseOps.add (DenseKernel.constant ![![-1,0,0],![1/4,0,0],![1/4,0,0],![1/4,0,0]])
    (denseOps.add (DenseKernel.constant ![![4/7,0,0],0,0,0]).mulU
      (DenseKernel.constant ![![4/7,0,0],0,0,0]).mulV)

theorem majorantBaseDense_real (u v t : ℝ) :
    majorantBaseDense.real u v t=(4/7)*(u+v)-1+(1/4)*Real.log 7 := by
  simp only [majorantBaseDense,(denseSound u v t).add,
    DenseKernel.mulU_real,DenseKernel.mulV_real,DenseKernel.constant_real]
  norm_num [KernelCoeff.real,AlgebraicCoeff.real,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
    Function.comp_def]
  linear_combination (1/4)*logConstants_sum

def majorantDense (pieces : Fin 7 → DenseKernel) : DenseKernel :=
  denseOps.add majorantBaseDense (denseOps.add (denseOps.scale (-1) (kernelDenseSum pieces))
    (denseOps.scale (-1/14) (denseOps.add (DenseKernel.diagonalAt 0 (kernelDenseSum pieces))
      (DenseKernel.diagonalAt 1 (kernelDenseSum pieces)))))

theorem majorantDense_real (pieces : Fin 7 → DenseKernel)
    (hp : ∀ k u v t,(pieces k).real u v t=kernelPiece k u v t) (u v t : ℝ) :
    (majorantDense pieces).real u v t=majorantFromMatrices u v t := by
  simp only [majorantDense,(denseSound u v t).add,(denseSound u v t).scale,
    majorantBaseDense_real,DenseKernel.diagonalAt_real,axisValue,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  simp_rw [kernelDenseSum_real pieces hp]
  dsimp [majorantFromMatrices]
  norm_num
  ring

end MordellEight
