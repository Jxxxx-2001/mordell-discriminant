import N7.Kernel.Local.Parameters
import N7.Kernel.LocalSchur
import N7.Kernel.Local.C2H00
import N7.Kernel.Local.C2H01
import N7.Kernel.Local.C2H02
import N7.Kernel.Local.C2H11
import N7.Kernel.Local.C2H12
import N7.Kernel.Local.C2H22
set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 0
namespace N7.Kernel.Local.C2
open Checks GapAnalytic LocalGeometry Matrix
def indices : Fin 3 → Fin 3 := id
def polys : Fin 3 → Fin 3 → DenseKernel := ![![C2H00.polynomial,C2H01.polynomial,C2H02.polynomial],![C2H01.polynomial,C2H11.polynomial,C2H12.polynomial],![C2H02.polynomial,C2H12.polynomial,C2H22.polynomial]]
theorem polys_real (i j : Fin 3) (x : Fin 3 → ℝ) : (polys i j).real (x 0-center 0) (x 1-center 1) (x 2-center 2)=eval3 (partialPoly (partialPoly exactMajorant (indices i)) (indices j)) x := by
  fin_cases i <;> fin_cases j
  · have h := C2H00.polynomial_real (x 0-center 0) (x 1-center 1) (x 2-center 2)
    simpa [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,polys,indices,center,point,eval3,partialPoly,Matrix.cons_val_two] using h
  · have h := C2H01.polynomial_real (x 0-center 0) (x 1-center 1) (x 2-center 2)
    simpa [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,polys,indices,center,point,eval3,partialPoly,Matrix.cons_val_two] using h
  · have h := C2H02.polynomial_real (x 0-center 0) (x 1-center 1) (x 2-center 2)
    simpa [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,polys,indices,center,point,eval3,partialPoly,Matrix.cons_val_two] using h
  · rw [mixed_partials]
    have h := C2H01.polynomial_real (x 0-center 0) (x 1-center 1) (x 2-center 2)
    simpa [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,polys,indices,center,point,eval3,partialPoly,Matrix.cons_val_two] using h
  · have h := C2H11.polynomial_real (x 0-center 0) (x 1-center 1) (x 2-center 2)
    simpa [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,polys,indices,center,point,eval3,partialPoly,Matrix.cons_val_two] using h
  · have h := C2H12.polynomial_real (x 0-center 0) (x 1-center 1) (x 2-center 2)
    simpa [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,polys,indices,center,point,eval3,partialPoly,Matrix.cons_val_two] using h
  · rw [mixed_partials]
    have h := C2H02.polynomial_real (x 0-center 0) (x 1-center 1) (x 2-center 2)
    simpa [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,polys,indices,center,point,eval3,partialPoly,Matrix.cons_val_two] using h
  · rw [mixed_partials]
    have h := C2H12.polynomial_real (x 0-center 0) (x 1-center 1) (x 2-center 2)
    simpa [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,polys,indices,center,point,eval3,partialPoly,Matrix.cons_val_two] using h
  · have h := C2H22.polynomial_real (x 0-center 0) (x 1-center 1) (x 2-center 2)
    simpa [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,polys,indices,center,point,eval3,partialPoly,Matrix.cons_val_two] using h

#print axioms polys_real
end N7.Kernel.Local.C2
