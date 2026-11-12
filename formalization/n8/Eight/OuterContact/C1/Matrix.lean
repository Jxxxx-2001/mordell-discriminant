import Eight.OuterContact.C1.H00
import Eight.OuterContact.C1.H01
import Eight.OuterContact.C1.H02
import Eight.OuterContact.C1.H11
import Eight.OuterContact.C1.H12
import Eight.OuterContact.C1.H22
import Eight.OuterContact.Analytic
namespace MordellEight.OuterContact.C1
open Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def q : ℚ := (40861/65536)
def radius : ℚ := (1/65536)
def polynomials : Fin 3 → Fin 3 → DenseKernel :=
  ![![H00.polynomial,H01.polynomial,H02.polynomial],![H01.polynomial,H11.polynomial,H12.polynomial],![H02.polynomial,H12.polynomial,H22.polynomial]]
def bounds (i j : Fin 3) : QInterval := ((polynomials i j).bound radius).add ((inverseBounds q radius).scale (ddQ i*ddQ j))
def C : Matrix (Fin 3) (Fin 3) ℚ := !![(117949749/625000000),(1835528197/10000000000),(-1886166291/5000000000);(1835528197/10000000000),(117949749/625000000),(-1886166291/5000000000);(-1886166291/5000000000),(-1886166291/5000000000),(11739920583/10000000000)]
def U : Matrix (Fin 3) (Fin 3) ℚ := !![1,(1835528197/1836308178),(-628722097/306051363);0,1,(-3772332582/3671836375);0,0,1]
def R : Matrix (Fin 3) (Fin 3) ℚ := !![1,(-1835528197/1836308178),(3772332582/3671836375);0,1,(3772332582/3671836375);0,0,1]
def D : Fin 3 → ℚ := ![(918154089/5000000000),(22911700860871/146904654240000000),(14459229520718289927/36718363750000000000)]
def error : ℚ := (8481301/5000000000)
theorem checked : intervalMatrixCheck bounds C U R D error=true := by decide +kernel
theorem distance_min_pos : (0:ℚ)<2-2*q-4*radius := by norm_num [q,radius]
theorem contact_check : algebraicCenterCheck 1 q radius=true := by decide +kernel
end MordellEight.OuterContact.C1
