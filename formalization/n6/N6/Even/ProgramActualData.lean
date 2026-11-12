import N6.ResultantMinors.Data
import N6.ResultantMinors.CoefficientCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Even.ProgramData
open N6.SparseCheck
def evenPart : Poly → Poly
  | [] => []
  | a::p => if a.1.b=0 ∧ a.1.k=0 then a::evenPart p else evenPart p
def actualDEvenDataPart0 : Poly := [(⟨0,1,0,4,0⟩,(64 : Int)), (⟨0,1,0,5,0⟩,(-512 : Int)), (⟨0,1,0,6,0⟩,(1024 : Int)), (⟨0,2,0,2,0⟩,(-512 : Int)), (⟨0,2,0,3,0⟩,(4352 : Int)), (⟨0,2,0,4,0⟩,(-9216 : Int)), (⟨0,3,0,0,0⟩,(1024 : Int)), (⟨0,3,0,1,0⟩,(-9216 : Int)), (⟨0,3,0,2,0⟩,(17280 : Int)), (⟨0,3,0,3,0⟩,(13824 : Int)), (⟨0,4,0,0,0⟩,(13824 : Int)), (⟨0,4,0,1,0⟩,(-62208 : Int)), (⟨0,5,0,0,0⟩,(46656 : Int))]
def actualDEvenData : Poly := actualDEvenDataPart0
def actualR4EvenDataPart0 : Poly := [(⟨0,0,0,5,0⟩,(64 : Int)), (⟨0,0,0,6,0⟩,(-512 : Int)), (⟨0,0,0,7,0⟩,(1024 : Int)), (⟨0,1,0,3,0⟩,(512 : Int)), (⟨0,1,0,4,0⟩,(-2816 : Int)), (⟨0,1,0,5,0⟩,(3072 : Int)), (⟨0,2,0,1,0⟩,(-3072 : Int)), (⟨0,2,0,2,0⟩,(12288 : Int)), (⟨0,2,0,3,0⟩,(26496 : Int)), (⟨0,2,0,4,0⟩,(-96768 : Int)), (⟨0,3,0,0,0⟩,(36864 : Int)), (⟨0,3,0,1,0⟩,(-290304 : Int)), (⟨0,3,0,2,0⟩,(518400 : Int)), (⟨0,4,0,0,0⟩,(248832 : Int)), (⟨0,4,0,1,0⟩,(-699840 : Int))]
def actualR4EvenData : Poly := actualR4EvenDataPart0
def actualR02EvenDataPart0 : Poly := [(⟨0,0,0,4,0⟩,(1600 : Int)), (⟨0,0,0,5,0⟩,(-11776 : Int)), (⟨0,0,0,6,0⟩,(21504 : Int)), (⟨0,1,0,2,0⟩,(-23040 : Int)), (⟨0,1,0,3,0⟩,(294144 : Int)), (⟨0,1,0,4,0⟩,(-1382400 : Int)), (⟨0,1,0,5,0⟩,(2322432 : Int)), (⟨0,2,0,0,0⟩,(82944 : Int)), (⟨0,2,0,1,0⟩,(-1188864 : Int)), (⟨0,2,0,2,0⟩,(6708096 : Int)), (⟨0,2,0,3,0⟩,(-13561344 : Int)), (⟨0,3,0,0,0⟩,(-1700352 : Int)), (⟨0,3,0,1,0⟩,(4665600 : Int)), (⟨0,3,0,2,0⟩,(18662400 : Int)), (⟨0,4,0,0,0⟩,(-17496000 : Int))]
def actualR02EvenData : Poly := actualR02EvenDataPart0
end N6.Even.ProgramData
