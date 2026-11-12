import N6.BranchEval.ProgramCore

set_option maxRecDepth 64000
set_option maxHeartbeats 6000000

namespace N6.BranchEval.B3.ProgramData
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

def factorDataPart0 : Poly := [(pm0, (561566973952 : Int)), (pm1, (117559076585472 : Int)), (pm2, (5099283647299584 : Int)), (pm3, (-16432753176207360 : Int)), (pm4, (17203943250590400 : Int)), (pm5, (-2742110206354125 : Int)), (pm6, (139471376040000 : Int))]
def factorData : Poly := factorDataPart0

def input0NumPart0 : Poly := [(pm1, (1 : Int))]
def input0Num : Poly := input0NumPart0

def input0NF : NF := ⟨input0Num, (1 : Int)⟩

def input1NumPart0 : Poly := [(pm0, (5599582009632711561776541466624 : Int)), (pm1, (-172071072403354666372251319271424 : Int)), (pm2, (517648976728852103708516826218496 : Int)), (pm3, (-466400880981335145422335320074880 : Int)), (pm4, (72798197302709589653652516136425 : Int)), (pm5, (-3664345858523843250463009416000 : Int))]
def input1Num : Poly := input1NumPart0

def input1NF : NF := ⟨input1Num, (30710995298801921896552020836352 : Int)⟩

def input2NumPart0 : Poly := [(pm0, (3452792234645085431113086664704 : Int)), (pm1, (27274924637269253925026097659904 : Int)), (pm2, (-105114483328506665421824087058432 : Int)), (pm3, (121565831617998963159594285728160 : Int)), (pm4, (-19606930466680795183143770866725 : Int)), (pm5, (1002938350110619699469256552000 : Int))]
def input2Num : Poly := input2NumPart0

def input2NF : NF := ⟨input2Num, (6398124020583733728448337674240 : Int)⟩

def input3NumPart0 : Poly := [(pm0, (-8815404604736149896009072246784 : Int)), (pm1, (-1181829790986949880493950727880704 : Int)), (pm2, (3582917490468641098145483986255872 : Int)), (pm3, (-3579102348684479514007901986642560 : Int)), (pm4, (566765445390544933680311882205975 : Int)), (pm5, (-28722613838443650531414465912000 : Int))]
def input3Num : Poly := input3NumPart0

def input3NF : NF := ⟨input3Num, (1381994788446086485344840937635840 : Int)⟩

def input4NumPart0 : Poly := [(pm0, (-11259742414418092495274751557632 : Int)), (pm1, (-2361570413757072854468617745989632 : Int)), (pm2, (-102344405382586230246308793685377024 : Int)), (pm3, (342050421054931907426017054085692800 : Int)), (pm4, (-379903994198704376991916844263061175 : Int)), (pm5, (84698623481313213157387234454136000 : Int))]
def input4Num : Poly := input4NumPart0

def input4NF : NF := ⟨input4Num, (13835552684013020981365205981184000 : Int)⟩

def input5NumPart0 : Poly := [(pm0, (89058702107339934214654001152 : Int)), (pm1, (17642837230963779408809446342656 : Int)), (pm2, (743552997954208645372926132584448 : Int)), (pm3, (-2504882224473328461777609977557632 : Int)), (pm4, (2837148489325283507923172916145005 : Int)), (pm5, (-677209980151750858036725839169600 : Int))]
def input5Num : Poly := input5NumPart0

def input5NF : NF := ⟨input5Num, (6832371695808899250056891842560 : Int)⟩

def input6NumPart0 : Poly := [(pm0, (-298783218481311868953987051945984 : Int)), (pm1, (-58676473618176583693859718060048384 : Int)), (pm2, (182469906485033909750357731374735360 : Int)), (pm3, (-188506103517558345156356411171150400 : Int)), (pm4, (29996934041699023372089997947397875 : Int)), (pm5, (-1524573930757927850229024042840000 : Int))]
def input6Num : Poly := input6NumPart0

def input6NF : NF := ⟨input6Num, (319906201029186686422416883712 : Int)⟩

end N6.BranchEval.B3.ProgramData
