import N6.BranchEval.ProgramCore

set_option maxRecDepth 64000
set_option maxHeartbeats 6000000

namespace N6.BranchEval.B2.ProgramData
open N6.SparseCheck N6.BranchEval.Program

def pm0 : Mon := ⟨0,0,0,0,0⟩
def pm1 : Mon := ⟨0,0,0,0,1⟩
def pm2 : Mon := ⟨0,0,0,0,2⟩
def pm3 : Mon := ⟨0,0,0,0,3⟩
def pm4 : Mon := ⟨0,0,0,0,4⟩
def pm5 : Mon := ⟨0,0,0,0,5⟩
def pm6 : Mon := ⟨0,0,0,0,6⟩
def pm7 : Mon := ⟨0,0,0,0,7⟩
def pm8 : Mon := ⟨0,0,0,0,8⟩
def pm9 : Mon := ⟨0,0,0,0,9⟩
def pm10 : Mon := ⟨0,0,0,0,10⟩
def pm11 : Mon := ⟨0,0,0,0,11⟩
def pm12 : Mon := ⟨0,0,0,0,12⟩
def pm13 : Mon := ⟨0,0,0,0,13⟩
def pm14 : Mon := ⟨0,0,0,0,14⟩
def pm15 : Mon := ⟨0,0,0,0,15⟩
def pm16 : Mon := ⟨0,0,0,0,16⟩
def pm17 : Mon := ⟨0,0,0,0,17⟩
def pm18 : Mon := ⟨0,0,0,0,18⟩
def pm19 : Mon := ⟨0,0,0,0,19⟩
def pm20 : Mon := ⟨0,0,0,0,20⟩
def pm21 : Mon := ⟨0,0,0,0,21⟩
def pm22 : Mon := ⟨0,0,0,0,22⟩
def pm23 : Mon := ⟨0,0,0,0,23⟩
def pm24 : Mon := ⟨0,0,0,0,24⟩
def pm25 : Mon := ⟨0,0,0,0,25⟩
def pm26 : Mon := ⟨0,0,0,0,26⟩

def factorDataPart0 : Poly := [(pm0, (-2048 : Int)), (pm1, (-71712 : Int)), (pm2, (3645 : Int))]
def factorData : Poly := factorDataPart0

def input0NumPart0 : Poly := [(pm1, (1 : Int))]
def input0Num : Poly := input0NumPart0

def input0NF : NF := ⟨input0Num, (1 : Int)⟩

def input1NumPart0 : Poly := [(pm0, (64 : Int)), (pm1, (243 : Int))]
def input1Num : Poly := input1NumPart0

def input1NF : NF := ⟨input1Num, (416 : Int)⟩

def input2NumPart0 : Poly := [(pm0, (4 : Int)), (pm1, (81 : Int))]
def input2Num : Poly := input2NumPart0

def input2NF : NF := ⟨input2Num, (260 : Int)⟩

def input3NumPart0 : Poly := [(pm0, (-448 : Int)), (pm1, (-16287 : Int))]
def input3Num : Poly := input3NumPart0

def input3NF : NF := ⟨input3Num, (6240 : Int)⟩

def input4NumPart0 : Poly := [(pm0, (-878710483730432 : Int)), (pm1, (-30813195508259328 : Int))]
def input4Num : Poly := input4NumPart0

def input4NF : NF := ⟨input4Num, (8125 : Int)⟩

def input5NumPart0 : Poly := [(pm0, (-51407458025472 : Int)), (pm1, (-1802673444837888 : Int))]
def input5Num : Poly := input5NumPart0

def input5NF : NF := ⟨input5Num, (325 : Int)⟩

def input6NumPart0 : Poly := [(pm0, (71892 : Int)), (pm1, (-3645 : Int))]
def input6Num : Poly := input6NumPart0

def input6NF : NF := ⟨input6Num, (52 : Int)⟩

end N6.BranchEval.B2.ProgramData
