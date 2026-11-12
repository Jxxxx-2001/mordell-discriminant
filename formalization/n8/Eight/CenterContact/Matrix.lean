import Eight.CenterContact.H00
import Eight.CenterContact.H01
import Eight.CenterContact.H02
import Eight.CenterContact.H11
import Eight.CenterContact.H12
import Eight.CenterContact.H22
import Eight.GapAnalytic
import Eight.Checks.IntervalMatrix

namespace MordellEight.CenterContact
open Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def radius : ℚ := (1/4096)
def polynomials : Fin 3 → Fin 3 → DenseKernel :=
  ![![H00.polynomial,H01.polynomial,H02.polynomial],![H01.polynomial,H11.polynomial,H12.polynomial],![H02.polynomial,H12.polynomial,H22.polynomial]]
def inverseDistanceBounds : QInterval := ⟨1/(1+4*radius)^2,1/(1-4*radius)^2⟩
def ddQ : Fin 3 → ℚ := ![1,1,-2]
def bounds (i j : Fin 3) : QInterval := ((polynomials i j).bound radius).add (inverseDistanceBounds.scale (ddQ i*ddQ j))
def C : Matrix (Fin 3) (Fin 3) ℚ := !![(366957687/1250000000),(2177949293/10000000000),(-1818720597/10000000000);(2177949293/10000000000),(2037963299/5000000000),(-1703131259/5000000000);(-1818720597/10000000000),(-1703131259/5000000000),(4462216143/10000000000)]
def U : Matrix (Fin 3) (Fin 3) ℚ := !![1,(167534561/196858617),(-606240199/853054007);0,1,(-365853571632364689/363382328443053518);0,0,1]
def R : Matrix (Fin 3) (Fin 3) ℚ := !![1,(-167534561/196858617),(-690442737149947343/4723970269759695734);0,1,(365853571632364689/363382328443053518);0,0,1]
def D : Fin 3 → ℚ := ![(2559162021/10000000000),(181691164221526759/984293085000000000),(4356013491736536619175268357/47239702697596957340000000000)]
def error : ℚ := (5019993/400000000)
theorem checked : intervalMatrixCheck bounds C U R D error=true := by decide +kernel
end MordellEight.CenterContact
