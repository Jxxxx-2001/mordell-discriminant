import Eight.AlgebraicEvaluation
import Eight.CoefficientBounds

namespace MordellEight

def contactU : Fin 4 → AlgebraicCoeff := ![0,AlgebraicCoeff.one,AlgebraicCoeff.one,AlgebraicCoeff.one]
def contactV : Fin 4 → AlgebraicCoeff := fun _ => AlgebraicCoeff.one
def contactT : Fin 4 → AlgebraicCoeff := ![0,![0,1,0],![-1,0,2],![1/2,-1,-2]]
def contactDistance : Fin 4 → AlgebraicCoeff :=
  ![AlgebraicCoeff.one,![2,-2,0],![4,0,-4],![1,2,4]]
def contactValue : Fin 4 → KernelCoeff :=
  ![0,![0,AlgebraicCoeff.one,0,0],![0,0,AlgebraicCoeff.one,0],![0,0,0,AlgebraicCoeff.one]]
def constantCoefficient (q : ℚ) : KernelCoeff := ![![q,0,0],0,0,0]

theorem constantCoefficient_real (q : ℚ) : (constantCoefficient q).real=(q : ℝ) := by
  simp [constantCoefficient,KernelCoeff.real,AlgebraicCoeff.real,Fin.sum_univ_succ]

theorem contactDistance_real (j : Fin 4) :
    (contactDistance j).real=(contactU j).real+(contactV j).real-2*(contactT j).real := by
  fin_cases j <;>
    norm_num [contactDistance,contactU,contactV,contactT,AlgebraicCoeff.one,
      AlgebraicCoeff.real,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem contactDistance_pos (j : Fin 4) : 0<(contactDistance j).real := by
  fin_cases j
  · norm_num [contactDistance,AlgebraicCoeff.one,AlgebraicCoeff.real,Matrix.cons_val_two]
  · convert distanceParameters_pos 0 using 1 <;>
      norm_num [contactDistance,AlgebraicCoeff.real,distanceParameters,cosineValues,Matrix.cons_val_two] <;> ring
  · convert distanceParameters_pos 1 using 1 <;>
      norm_num [contactDistance,AlgebraicCoeff.real,distanceParameters,cosineValues,
        Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> ring
  · convert distanceParameters_pos 2 using 1 <;>
      norm_num [contactDistance,AlgebraicCoeff.real,distanceParameters,cosineValues,
        Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem contactValue_real (j : Fin 4) :
    (contactValue j).real=Real.log ((contactDistance j).real) := by
  fin_cases j <;>
    norm_num [contactValue,contactDistance,AlgebraicCoeff.one,AlgebraicCoeff.real,
      KernelCoeff.real,Fin.sum_univ_succ,logConstants,distanceParameters,cosineValues,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> congr 1 <;> ring

end MordellEight
