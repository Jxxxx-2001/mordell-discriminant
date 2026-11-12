import Eight.OuterContact.C2.H00
import Eight.OuterContact.C2.H01
import Eight.OuterContact.C2.H02
import Eight.OuterContact.C2.H11
import Eight.OuterContact.C2.H12
import Eight.OuterContact.C2.H22
import Eight.OuterContact.Analytic
namespace MordellEight.OuterContact.C2
open Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def q : ℚ := (-116665/524288)
def radius : ℚ := (1/2048)
def polynomials : Fin 3 → Fin 3 → DenseKernel :=
  ![![H00.polynomial,H01.polynomial,H02.polynomial],![H01.polynomial,H11.polynomial,H12.polynomial],![H02.polynomial,H12.polynomial,H22.polynomial]]
def bounds (i j : Fin 3) : QInterval := ((polynomials i j).bound radius).add ((inverseBounds q radius).scale (ddQ i*ddQ j))
def C : Matrix (Fin 3) (Fin 3) ℚ := !![(59914879/625000000),(897327371/10000000000),(-41284989/2000000000);(897327371/10000000000),(59914879/625000000),(-41284989/2000000000);(-41284989/2000000000),(-41284989/2000000000),(333739781/5000000000)]
def U : Matrix (Fin 3) (Fin 3) ℚ := !![1,(897327371/904846990),(-41284989/180969398);0,1,(-68808315/600724787);0,0,1]
def R : Matrix (Fin 3) (Fin 3) ℚ := !![1,(-897327371/904846990),(68808315/600724787);0,1,(68808315/600724787);0,0,1]
def D : Fin 3 → ℚ := ![(90484699/1000000000),(13551664566288459/9048469900000000000),(170125190479658353/3003623935000000000)]
def error : ℚ := (8965179/5000000000)
theorem checked : intervalMatrixCheck bounds C U R D error=true := by decide +kernel
theorem distance_min_pos : (0:ℚ)<2-2*q-4*radius := by norm_num [q,radius]
theorem contact_check : algebraicCenterCheck 2 q radius=true := by decide +kernel
end MordellEight.OuterContact.C2
