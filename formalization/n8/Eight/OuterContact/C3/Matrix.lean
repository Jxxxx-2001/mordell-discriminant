import Eight.OuterContact.C3.H00
import Eight.OuterContact.C3.H01
import Eight.OuterContact.C3.H02
import Eight.OuterContact.C3.H11
import Eight.OuterContact.C3.H12
import Eight.OuterContact.C3.H22
import Eight.OuterContact.Analytic
namespace MordellEight.OuterContact.C3
open Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def q : ℚ := (-472367/524288)
def radius : ℚ := (1/256)
def polynomials : Fin 3 → Fin 3 → DenseKernel :=
  ![![H00.polynomial,H01.polynomial,H02.polynomial],![H01.polynomial,H11.polynomial,H12.polynomial],![H02.polynomial,H12.polynomial,H22.polynomial]]
def bounds (i j : Fin 3) : QInterval := ((polynomials i j).bound radius).add ((inverseBounds q radius).scale (ddQ i*ddQ j))
def C : Matrix (Fin 3) (Fin 3) ℚ := !![(414660213/5000000000),(54506121/5000000000),(32127233/1000000000);(54506121/5000000000),(414660213/5000000000),(32127233/1000000000);(32127233/1000000000),(32127233/1000000000),(221780077/2000000000)]
def U : Matrix (Fin 3) (Fin 3) ℚ := !![1,(18168707/80997951),(160636165/242993853);0,1,(160636165/297499974);0,0,1]
def R : Matrix (Fin 3) (Fin 3) ℚ := !![1,(-18168707/80997951),(-160636165/297499974);0,1,(-160636165/297499974);0,0,1]
def D : Fin 3 → ℚ := ![(242993853/5000000000),(778820769018319/16874573125000000),(12454045040911181/297499974000000000)]
def error : ℚ := (1430553/125000000)
theorem checked : intervalMatrixCheck bounds C U R D error=true := by decide +kernel
theorem distance_min_pos : (0:ℚ)<2-2*q-4*radius := by norm_num [q,radius]
theorem contact_check : algebraicCenterCheck 3 q radius=true := by decide +kernel
end MordellEight.OuterContact.C3
