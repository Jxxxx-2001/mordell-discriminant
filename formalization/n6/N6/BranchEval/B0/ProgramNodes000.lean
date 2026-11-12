import N6.BranchEval.B0.ProgramInputs

set_option maxRecDepth 64000
set_option maxHeartbeats 6000000

namespace N6.BranchEval.B0.ProgramData
open N6.SparseCheck N6.BranchEval.Program

def n0000NumPart0 : Poly := [(pm0, (64 : Int))]
def n0000Num : Poly := n0000NumPart0

def n0000NF : NF := ⟨n0000Num, (9 : Int)⟩

def n0000QPart0 : Poly := [(pm0, (1 : Int))]
def n0000Q : Poly := n0000QPart0

def n0000Row : Row := ⟨n0000NF, .input 0, (1 : Int), n0000Q⟩

def n0001NumPart0 : Poly := [(pm0, (3 : Int))]
def n0001Num : Poly := n0001NumPart0

def n0001NF : NF := ⟨n0001Num, (1 : Int)⟩

def n0001QPart0 : Poly := []
def n0001Q : Poly := n0001QPart0

def n0001Row : Row := ⟨n0001NF, .input 1, (1 : Int), n0001Q⟩

def n0002NumPart0 : Poly := [(pm0, (-1 : Int))]
def n0002Num : Poly := n0002NumPart0

def n0002NF : NF := ⟨n0002Num, (1 : Int)⟩

def n0002QPart0 : Poly := []
def n0002Q : Poly := n0002QPart0

def n0002Row : Row := ⟨n0002NF, .input 2, (1 : Int), n0002Q⟩

def n0003NumPart0 : Poly := [(pm0, (19 : Int))]
def n0003Num : Poly := n0003NumPart0

def n0003NF : NF := ⟨n0003Num, (9 : Int)⟩

def n0003QPart0 : Poly := []
def n0003Q : Poly := n0003QPart0

def n0003Row : Row := ⟨n0003NF, .input 3, (1 : Int), n0003Q⟩

def n0004NumPart0 : Poly := [(pm0, (-1 : Int))]
def n0004Num : Poly := n0004NumPart0

def n0004NF : NF := ⟨n0004Num, (1 : Int)⟩

def n0004QPart0 : Poly := []
def n0004Q : Poly := n0004QPart0

def n0004Row : Row := ⟨n0004NF, .lit (-1 : Int) (1 : Int), (1 : Int), n0004Q⟩

def n0005NumPart0 : Poly := [(pm0, (108 : Int))]
def n0005Num : Poly := n0005NumPart0

def n0005NF : NF := ⟨n0005Num, (1 : Int)⟩

def n0005QPart0 : Poly := []
def n0005Q : Poly := n0005QPart0

def n0005Row : Row := ⟨n0005NF, .lit (108 : Int) (1 : Int), (1 : Int), n0005Q⟩

def n0006NumPart0 : Poly := [(pm0, (-108 : Int))]
def n0006Num : Poly := n0006NumPart0

def n0006NF : NF := ⟨n0006Num, (1 : Int)⟩

def n0006QPart0 : Poly := []
def n0006Q : Poly := n0006QPart0

def n0006Row : Row := ⟨n0006NF, .mul 4 5, (1 : Int), n0006Q⟩

def n0007NumPart0 : Poly := [(pm0, (4096 : Int))]
def n0007Num : Poly := n0007NumPart0

def n0007NF : NF := ⟨n0007Num, (81 : Int)⟩

def n0007QPart0 : Poly := []
def n0007Q : Poly := n0007QPart0

def n0007Row : Row := ⟨n0007NF, .mul 0 0, (1 : Int), n0007Q⟩

def n0008NumPart0 : Poly := [(pm0, (16777216 : Int))]
def n0008Num : Poly := n0008NumPart0

def n0008NF : NF := ⟨n0008Num, (6561 : Int)⟩

def n0008QPart0 : Poly := []
def n0008Q : Poly := n0008QPart0

def n0008Row : Row := ⟨n0008NF, .mul 7 7, (1 : Int), n0008Q⟩

def n0009NumPart0 : Poly := [(pm0, (-67108864 : Int))]
def n0009Num : Poly := n0009NumPart0

def n0009NF : NF := ⟨n0009Num, (243 : Int)⟩

def n0009QPart0 : Poly := []
def n0009Q : Poly := n0009QPart0

def n0009Row : Row := ⟨n0009NF, .mul 6 8, (1 : Int), n0009Q⟩

def n0010NumPart0 : Poly := [(pm0, (1 : Int))]
def n0010Num : Poly := n0010NumPart0

def n0010NF : NF := ⟨n0010Num, (1 : Int)⟩

def n0010QPart0 : Poly := []
def n0010Q : Poly := n0010QPart0

def n0010Row : Row := ⟨n0010NF, .mul 2 2, (1 : Int), n0010Q⟩

def n0011NumPart0 : Poly := [(pm0, (-1 : Int))]
def n0011Num : Poly := n0011NumPart0

def n0011NF : NF := ⟨n0011Num, (1 : Int)⟩

def n0011QPart0 : Poly := []
def n0011Q : Poly := n0011QPart0

def n0011Row : Row := ⟨n0011NF, .mul 2 10, (1 : Int), n0011Q⟩

def n0012NumPart0 : Poly := [(pm0, (67108864 : Int))]
def n0012Num : Poly := n0012NumPart0

def n0012NF : NF := ⟨n0012Num, (243 : Int)⟩

def n0012QPart0 : Poly := []
def n0012Q : Poly := n0012QPart0

def n0012Row : Row := ⟨n0012NF, .mul 9 11, (1 : Int), n0012Q⟩

def n0013NumPart0 : Poly := [(pm0, (27 : Int))]
def n0013Num : Poly := n0013NumPart0

def n0013NF : NF := ⟨n0013Num, (1 : Int)⟩

def n0013QPart0 : Poly := []
def n0013Q : Poly := n0013QPart0

def n0013Row : Row := ⟨n0013NF, .lit (27 : Int) (1 : Int), (1 : Int), n0013Q⟩

def n0014NumPart0 : Poly := [(pm0, (262144 : Int))]
def n0014Num : Poly := n0014NumPart0

def n0014NF : NF := ⟨n0014Num, (729 : Int)⟩

def n0014QPart0 : Poly := []
def n0014Q : Poly := n0014QPart0

def n0014Row : Row := ⟨n0014NF, .mul 0 7, (1 : Int), n0014Q⟩

def n0015NumPart0 : Poly := [(pm0, (262144 : Int))]
def n0015Num : Poly := n0015NumPart0

def n0015NF : NF := ⟨n0015Num, (27 : Int)⟩

def n0015QPart0 : Poly := []
def n0015Q : Poly := n0015QPart0

def n0015Row : Row := ⟨n0015NF, .mul 13 14, (1 : Int), n0015Q⟩

def n0016NumPart0 : Poly := [(pm0, (9 : Int))]
def n0016Num : Poly := n0016NumPart0

def n0016NF : NF := ⟨n0016Num, (1 : Int)⟩

def n0016QPart0 : Poly := []
def n0016Q : Poly := n0016QPart0

def n0016Row : Row := ⟨n0016NF, .mul 1 1, (1 : Int), n0016Q⟩

def n0017NumPart0 : Poly := [(pm0, (262144 : Int))]
def n0017Num : Poly := n0017NumPart0

def n0017NF : NF := ⟨n0017Num, (3 : Int)⟩

def n0017QPart0 : Poly := []
def n0017Q : Poly := n0017QPart0

def n0017Row : Row := ⟨n0017NF, .mul 15 16, (1 : Int), n0017Q⟩

def n0018NumPart0 : Poly := [(pm0, (262144 : Int))]
def n0018Num : Poly := n0018NumPart0

def n0018NF : NF := ⟨n0018Num, (3 : Int)⟩

def n0018QPart0 : Poly := []
def n0018Q : Poly := n0018QPart0

def n0018Row : Row := ⟨n0018NF, .mul 10 17, (1 : Int), n0018Q⟩

def n0019NumPart0 : Poly := [(pm0, (88342528 : Int))]
def n0019Num : Poly := n0019NumPart0

def n0019NF : NF := ⟨n0019Num, (243 : Int)⟩

def n0019QPart0 : Poly := []
def n0019Q : Poly := n0019QPart0

def n0019Row : Row := ⟨n0019NF, .add 12 18, (1 : Int), n0019Q⟩

def n0020NumPart0 : Poly := [(pm0, (486 : Int))]
def n0020Num : Poly := n0020NumPart0

def n0020NF : NF := ⟨n0020Num, (1 : Int)⟩

def n0020QPart0 : Poly := []
def n0020Q : Poly := n0020QPart0

def n0020Row : Row := ⟨n0020NF, .lit (486 : Int) (1 : Int), (1 : Int), n0020Q⟩

def n0021NumPart0 : Poly := [(pm0, (524288 : Int))]
def n0021Num : Poly := n0021NumPart0

def n0021NF : NF := ⟨n0021Num, (3 : Int)⟩

def n0021QPart0 : Poly := []
def n0021Q : Poly := n0021QPart0

def n0021Row : Row := ⟨n0021NF, .mul 14 20, (1 : Int), n0021Q⟩

def n0022NumPart0 : Poly := [(pm0, (524288 : Int))]
def n0022Num : Poly := n0022NumPart0

def n0022NF : NF := ⟨n0022Num, (1 : Int)⟩

def n0022QPart0 : Poly := []
def n0022Q : Poly := n0022QPart0

def n0022Row : Row := ⟨n0022NF, .mul 1 21, (1 : Int), n0022Q⟩

def n0023NumPart0 : Poly := [(pm0, (9961472 : Int))]
def n0023Num : Poly := n0023NumPart0

def n0023NF : NF := ⟨n0023Num, (9 : Int)⟩

def n0023QPart0 : Poly := []
def n0023Q : Poly := n0023QPart0

def n0023Row : Row := ⟨n0023NF, .mul 3 22, (1 : Int), n0023Q⟩

def n0024NumPart0 : Poly := [(pm0, (-9961472 : Int))]
def n0024Num : Poly := n0024NumPart0

def n0024NF : NF := ⟨n0024Num, (9 : Int)⟩

def n0024QPart0 : Poly := []
def n0024Q : Poly := n0024QPart0

def n0024Row : Row := ⟨n0024NF, .mul 2 23, (1 : Int), n0024Q⟩

def n0025NumPart0 : Poly := [(pm0, (-180617216 : Int))]
def n0025Num : Poly := n0025NumPart0

def n0025NF : NF := ⟨n0025Num, (243 : Int)⟩

def n0025QPart0 : Poly := []
def n0025Q : Poly := n0025QPart0

def n0025Row : Row := ⟨n0025NF, .add 19 24, (1 : Int), n0025Q⟩

def n0026NumPart0 : Poly := [(pm0, (2250 : Int))]
def n0026Num : Poly := n0026NumPart0

def n0026NF : NF := ⟨n0026Num, (1 : Int)⟩

def n0026QPart0 : Poly := []
def n0026Q : Poly := n0026QPart0

def n0026Row : Row := ⟨n0026NF, .lit (2250 : Int) (1 : Int), (1 : Int), n0026Q⟩

def n0027NumPart0 : Poly := [(pm0, (65536000 : Int))]
def n0027Num : Poly := n0027NumPart0

def n0027NF : NF := ⟨n0027Num, (81 : Int)⟩

def n0027QPart0 : Poly := []
def n0027Q : Poly := n0027QPart0

def n0027Row : Row := ⟨n0027NF, .mul 14 26, (1 : Int), n0027Q⟩

def n0028NumPart0 : Poly := [(pm0, (65536000 : Int))]
def n0028Num : Poly := n0028NumPart0

def n0028NF : NF := ⟨n0028Num, (27 : Int)⟩

def n0028QPart0 : Poly := []
def n0028Q : Poly := n0028QPart0

def n0028Row : Row := ⟨n0028NF, .mul 1 27, (1 : Int), n0028Q⟩

def n0029NumPart0 : Poly := [(pm0, (1 : Int))]
def n0029Num : Poly := n0029NumPart0

def n0029NF : NF := ⟨n0029Num, (1 : Int)⟩

def n0029QPart0 : Poly := []
def n0029Q : Poly := n0029QPart0

def n0029Row : Row := ⟨n0029NF, .mul 10 10, (1 : Int), n0029Q⟩

def n0030NumPart0 : Poly := [(pm0, (65536000 : Int))]
def n0030Num : Poly := n0030NumPart0

def n0030NF : NF := ⟨n0030Num, (27 : Int)⟩

def n0030QPart0 : Poly := []
def n0030Q : Poly := n0030QPart0

def n0030Row : Row := ⟨n0030NF, .mul 28 29, (1 : Int), n0030Q⟩

def n0031NumPart0 : Poly := [(pm0, (-65536000 : Int))]
def n0031Num : Poly := n0031NumPart0

def n0031NF : NF := ⟨n0031Num, (27 : Int)⟩

def n0031QPart0 : Poly := []
def n0031Q : Poly := n0031QPart0

def n0031Row : Row := ⟨n0031NF, .mul 4 30, (1 : Int), n0031Q⟩

def n0032NumPart0 : Poly := [(pm0, (-770441216 : Int))]
def n0032Num : Poly := n0032NumPart0

def n0032NF : NF := ⟨n0032Num, (243 : Int)⟩

def n0032QPart0 : Poly := []
def n0032Q : Poly := n0032QPart0

def n0032Row : Row := ⟨n0032NF, .add 25 31, (1 : Int), n0032Q⟩

def n0033NumPart0 : Poly := [(pm0, (630 : Int))]
def n0033Num : Poly := n0033NumPart0

def n0033NF : NF := ⟨n0033Num, (1 : Int)⟩

def n0033QPart0 : Poly := []
def n0033Q : Poly := n0033QPart0

def n0033Row : Row := ⟨n0033NF, .lit (630 : Int) (1 : Int), (1 : Int), n0033Q⟩

def n0034NumPart0 : Poly := [(pm0, (18350080 : Int))]
def n0034Num : Poly := n0034NumPart0

def n0034NF : NF := ⟨n0034Num, (81 : Int)⟩

def n0034QPart0 : Poly := []
def n0034Q : Poly := n0034QPart0

def n0034Row : Row := ⟨n0034NF, .mul 14 33, (1 : Int), n0034Q⟩

def n0035NumPart0 : Poly := [(pm0, (18350080 : Int))]
def n0035Num : Poly := n0035NumPart0

def n0035NF : NF := ⟨n0035Num, (27 : Int)⟩

def n0035QPart0 : Poly := []
def n0035Q : Poly := n0035QPart0

def n0035Row : Row := ⟨n0035NF, .mul 1 34, (1 : Int), n0035Q⟩

def n0036NumPart0 : Poly := [(pm0, (-18350080 : Int))]
def n0036Num : Poly := n0036NumPart0

def n0036NF : NF := ⟨n0036Num, (27 : Int)⟩

def n0036QPart0 : Poly := []
def n0036Q : Poly := n0036QPart0

def n0036Row : Row := ⟨n0036NF, .mul 11 35, (1 : Int), n0036Q⟩

def n0037NumPart0 : Poly := [(pm0, (-935591936 : Int))]
def n0037Num : Poly := n0037NumPart0

def n0037NF : NF := ⟨n0037Num, (243 : Int)⟩

def n0037QPart0 : Poly := []
def n0037Q : Poly := n0037QPart0

def n0037Row : Row := ⟨n0037NF, .add 32 36, (1 : Int), n0037Q⟩

def n0038NumPart0 : Poly := [(pm0, (729 : Int))]
def n0038Num : Poly := n0038NumPart0

def n0038NF : NF := ⟨n0038Num, (1 : Int)⟩

def n0038QPart0 : Poly := []
def n0038Q : Poly := n0038QPart0

def n0038Row : Row := ⟨n0038NF, .lit (729 : Int) (1 : Int), (1 : Int), n0038Q⟩

def n0039NumPart0 : Poly := [(pm0, (262144 : Int))]
def n0039Num : Poly := n0039NumPart0

def n0039NF : NF := ⟨n0039Num, (1 : Int)⟩

def n0039QPart0 : Poly := []
def n0039Q : Poly := n0039QPart0

def n0039Row : Row := ⟨n0039NF, .mul 14 38, (1 : Int), n0039Q⟩

def n0040NumPart0 : Poly := [(pm0, (361 : Int))]
def n0040Num : Poly := n0040NumPart0

def n0040NF : NF := ⟨n0040Num, (81 : Int)⟩

def n0040QPart0 : Poly := []
def n0040Q : Poly := n0040QPart0

def n0040Row : Row := ⟨n0040NF, .mul 3 3, (1 : Int), n0040Q⟩

def n0041NumPart0 : Poly := [(pm0, (94633984 : Int))]
def n0041Num : Poly := n0041NumPart0

def n0041NF : NF := ⟨n0041Num, (81 : Int)⟩

def n0041QPart0 : Poly := []
def n0041Q : Poly := n0041QPart0

def n0041Row : Row := ⟨n0041NF, .mul 39 40, (1 : Int), n0041Q⟩

def n0042NumPart0 : Poly := [(pm0, (-94633984 : Int))]
def n0042Num : Poly := n0042NumPart0

def n0042NF : NF := ⟨n0042Num, (81 : Int)⟩

def n0042QPart0 : Poly := []
def n0042Q : Poly := n0042QPart0

def n0042Row : Row := ⟨n0042NF, .mul 4 41, (1 : Int), n0042Q⟩

def n0043NumPart0 : Poly := [(pm0, (-1219493888 : Int))]
def n0043Num : Poly := n0043NumPart0

def n0043NF : NF := ⟨n0043Num, (243 : Int)⟩

def n0043QPart0 : Poly := []
def n0043Q : Poly := n0043QPart0

def n0043Row : Row := ⟨n0043NF, .add 37 42, (1 : Int), n0043Q⟩

def n0044NumPart0 : Poly := [(pm0, (1350 : Int))]
def n0044Num : Poly := n0044NumPart0

def n0044NF : NF := ⟨n0044Num, (1 : Int)⟩

def n0044QPart0 : Poly := []
def n0044Q : Poly := n0044QPart0

def n0044Row : Row := ⟨n0044NF, .lit (1350 : Int) (1 : Int), (1 : Int), n0044Q⟩

def n0045NumPart0 : Poly := [(pm0, (13107200 : Int))]
def n0045Num : Poly := n0045NumPart0

def n0045NF : NF := ⟨n0045Num, (27 : Int)⟩

def n0045QPart0 : Poly := []
def n0045Q : Poly := n0045QPart0

def n0045Row : Row := ⟨n0045NF, .mul 14 44, (1 : Int), n0045Q⟩

def n0046NumPart0 : Poly := [(pm0, (249036800 : Int))]
def n0046Num : Poly := n0046NumPart0

def n0046NF : NF := ⟨n0046Num, (243 : Int)⟩

def n0046QPart0 : Poly := []
def n0046Q : Poly := n0046QPart0

def n0046Row : Row := ⟨n0046NF, .mul 3 45, (1 : Int), n0046Q⟩

def n0047NumPart0 : Poly := [(pm0, (-249036800 : Int))]
def n0047Num : Poly := n0047NumPart0

def n0047NF : NF := ⟨n0047Num, (243 : Int)⟩

def n0047QPart0 : Poly := []
def n0047Q : Poly := n0047QPart0

def n0047Row : Row := ⟨n0047NF, .mul 11 46, (1 : Int), n0047Q⟩

def n0048NumPart0 : Poly := [(pm0, (-1468530688 : Int))]
def n0048Num : Poly := n0048NumPart0

def n0048NF : NF := ⟨n0048Num, (243 : Int)⟩

def n0048QPart0 : Poly := []
def n0048Q : Poly := n0048QPart0

def n0048Row : Row := ⟨n0048NF, .add 43 47, (1 : Int), n0048Q⟩

def n0049NumPart0 : Poly := [(pm0, (162 : Int))]
def n0049Num : Poly := n0049NumPart0

def n0049NF : NF := ⟨n0049Num, (1 : Int)⟩

def n0049QPart0 : Poly := []
def n0049Q : Poly := n0049QPart0

def n0049Row : Row := ⟨n0049NF, .lit (162 : Int) (1 : Int), (1 : Int), n0049Q⟩

def n0050NumPart0 : Poly := [(pm0, (524288 : Int))]
def n0050Num : Poly := n0050NumPart0

def n0050NF : NF := ⟨n0050Num, (9 : Int)⟩

def n0050QPart0 : Poly := []
def n0050Q : Poly := n0050QPart0

def n0050Row : Row := ⟨n0050NF, .mul 14 49, (1 : Int), n0050Q⟩

def n0051NumPart0 : Poly := [(pm0, (9961472 : Int))]
def n0051Num : Poly := n0051NumPart0

def n0051NF : NF := ⟨n0051Num, (81 : Int)⟩

def n0051QPart0 : Poly := []
def n0051Q : Poly := n0051QPart0

def n0051Row : Row := ⟨n0051NF, .mul 3 50, (1 : Int), n0051Q⟩

def n0052NumPart0 : Poly := [(pm0, (9961472 : Int))]
def n0052Num : Poly := n0052NumPart0

def n0052NF : NF := ⟨n0052Num, (81 : Int)⟩

def n0052QPart0 : Poly := []
def n0052Q : Poly := n0052QPart0

def n0052Row : Row := ⟨n0052NF, .mul 10 51, (1 : Int), n0052Q⟩

def n0053NumPart0 : Poly := [(pm0, (-9961472 : Int))]
def n0053Num : Poly := n0053NumPart0

def n0053NF : NF := ⟨n0053Num, (81 : Int)⟩

def n0053QPart0 : Poly := []
def n0053Q : Poly := n0053QPart0

def n0053Row : Row := ⟨n0053NF, .mul 4 52, (1 : Int), n0053Q⟩

def n0054NumPart0 : Poly := [(pm0, (-1498415104 : Int))]
def n0054Num : Poly := n0054NumPart0

def n0054NF : NF := ⟨n0054Num, (243 : Int)⟩

def n0054QPart0 : Poly := []
def n0054Q : Poly := n0054QPart0

def n0054Row : Row := ⟨n0054NF, .add 48 53, (1 : Int), n0054Q⟩

def n0055NumPart0 : Poly := [(pm0, (3125 : Int))]
def n0055Num : Poly := n0055NumPart0

def n0055NF : NF := ⟨n0055Num, (1 : Int)⟩

def n0055QPart0 : Poly := []
def n0055Q : Poly := n0055QPart0

def n0055Row : Row := ⟨n0055NF, .lit (3125 : Int) (1 : Int), (1 : Int), n0055Q⟩

def n0056NumPart0 : Poly := [(pm0, (819200000 : Int))]
def n0056Num : Poly := n0056NumPart0

def n0056NF : NF := ⟨n0056Num, (729 : Int)⟩

def n0056QPart0 : Poly := []
def n0056Q : Poly := n0056QPart0

def n0056Row : Row := ⟨n0056NF, .mul 14 55, (1 : Int), n0056Q⟩

def n0057NumPart0 : Poly := [(pm0, (1 : Int))]
def n0057Num : Poly := n0057NumPart0

def n0057NF : NF := ⟨n0057Num, (1 : Int)⟩

def n0057QPart0 : Poly := []
def n0057Q : Poly := n0057QPart0

def n0057Row : Row := ⟨n0057NF, .mul 11 11, (1 : Int), n0057Q⟩

def n0058NumPart0 : Poly := [(pm0, (819200000 : Int))]
def n0058Num : Poly := n0058NumPart0

def n0058NF : NF := ⟨n0058Num, (729 : Int)⟩

def n0058QPart0 : Poly := []
def n0058Q : Poly := n0058QPart0

def n0058Row : Row := ⟨n0058NF, .mul 56 57, (1 : Int), n0058Q⟩

def n0059NumPart0 : Poly := [(pm0, (-819200000 : Int))]
def n0059Num : Poly := n0059NumPart0

def n0059NF : NF := ⟨n0059Num, (729 : Int)⟩

def n0059QPart0 : Poly := []
def n0059Q : Poly := n0059QPart0

def n0059Row : Row := ⟨n0059NF, .mul 4 58, (1 : Int), n0059Q⟩

def n0060NumPart0 : Poly := [(pm0, (-5314445312 : Int))]
def n0060Num : Poly := n0060NumPart0

def n0060NF : NF := ⟨n0060Num, (729 : Int)⟩

def n0060QPart0 : Poly := []
def n0060Q : Poly := n0060QPart0

def n0060Row : Row := ⟨n0060NF, .add 54 59, (1 : Int), n0060Q⟩

def n0061NumPart0 : Poly := [(pm0, (3750 : Int))]
def n0061Num : Poly := n0061NumPart0

def n0061NF : NF := ⟨n0061Num, (1 : Int)⟩

def n0061QPart0 : Poly := []
def n0061Q : Poly := n0061QPart0

def n0061Row : Row := ⟨n0061NF, .lit (3750 : Int) (1 : Int), (1 : Int), n0061Q⟩

def n0062NumPart0 : Poly := [(pm0, (327680000 : Int))]
def n0062Num : Poly := n0062NumPart0

def n0062NF : NF := ⟨n0062Num, (243 : Int)⟩

def n0062QPart0 : Poly := []
def n0062Q : Poly := n0062QPart0

def n0062Row : Row := ⟨n0062NF, .mul 14 61, (1 : Int), n0062Q⟩

def n0063NumPart0 : Poly := [(pm0, (-1 : Int))]
def n0063Num : Poly := n0063NumPart0

def n0063NF : NF := ⟨n0063Num, (1 : Int)⟩

def n0063QPart0 : Poly := []
def n0063Q : Poly := n0063QPart0

def n0063Row : Row := ⟨n0063NF, .mul 2 29, (1 : Int), n0063Q⟩

def n0064NumPart0 : Poly := [(pm0, (-327680000 : Int))]
def n0064Num : Poly := n0064NumPart0

def n0064NF : NF := ⟨n0064Num, (243 : Int)⟩

def n0064QPart0 : Poly := []
def n0064Q : Poly := n0064QPart0

def n0064Row : Row := ⟨n0064NF, .mul 62 63, (1 : Int), n0064Q⟩

def n0065NumPart0 : Poly := [(pm0, (-6297485312 : Int))]
def n0065Num : Poly := n0065NumPart0

def n0065NF : NF := ⟨n0065Num, (729 : Int)⟩

def n0065QPart0 : Poly := []
def n0065Q : Poly := n0065QPart0

def n0065Row : Row := ⟨n0065NF, .add 60 64, (1 : Int), n0065Q⟩

def n0066NumPart0 : Poly := [(pm0, (825 : Int))]
def n0066Num : Poly := n0066NumPart0

def n0066NF : NF := ⟨n0066Num, (1 : Int)⟩

def n0066QPart0 : Poly := []
def n0066Q : Poly := n0066QPart0

def n0066Row : Row := ⟨n0066NF, .lit (825 : Int) (1 : Int), (1 : Int), n0066Q⟩

def n0067NumPart0 : Poly := [(pm0, (72089600 : Int))]
def n0067Num : Poly := n0067NumPart0

def n0067NF : NF := ⟨n0067Num, (243 : Int)⟩

def n0067QPart0 : Poly := []
def n0067Q : Poly := n0067QPart0

def n0067Row : Row := ⟨n0067NF, .mul 14 66, (1 : Int), n0067Q⟩

def n0068NumPart0 : Poly := [(pm0, (72089600 : Int))]
def n0068Num : Poly := n0068NumPart0

def n0068NF : NF := ⟨n0068Num, (243 : Int)⟩

def n0068QPart0 : Poly := []
def n0068Q : Poly := n0068QPart0

def n0068Row : Row := ⟨n0068NF, .mul 29 67, (1 : Int), n0068Q⟩

def n0069NumPart0 : Poly := [(pm0, (-72089600 : Int))]
def n0069Num : Poly := n0069NumPart0

def n0069NF : NF := ⟨n0069Num, (243 : Int)⟩

def n0069QPart0 : Poly := []
def n0069Q : Poly := n0069QPart0

def n0069Row : Row := ⟨n0069NF, .mul 4 68, (1 : Int), n0069Q⟩

def n0070NumPart0 : Poly := [(pm0, (-6513754112 : Int))]
def n0070Num : Poly := n0070NumPart0

def n0070NF : NF := ⟨n0070Num, (729 : Int)⟩

def n0070QPart0 : Poly := []
def n0070Q : Poly := n0070QPart0

def n0070Row : Row := ⟨n0070NF, .add 65 69, (1 : Int), n0070Q⟩

def n0071NumPart0 : Poly := [(pm0, (16 : Int))]
def n0071Num : Poly := n0071NumPart0

def n0071NF : NF := ⟨n0071Num, (1 : Int)⟩

def n0071QPart0 : Poly := []
def n0071Q : Poly := n0071QPart0

def n0071Row : Row := ⟨n0071NF, .lit (16 : Int) (1 : Int), (1 : Int), n0071Q⟩

def n0072NumPart0 : Poly := [(pm0, (4194304 : Int))]
def n0072Num : Poly := n0072NumPart0

def n0072NF : NF := ⟨n0072Num, (729 : Int)⟩

def n0072QPart0 : Poly := []
def n0072Q : Poly := n0072QPart0

def n0072Row : Row := ⟨n0072NF, .mul 14 71, (1 : Int), n0072Q⟩

def n0073NumPart0 : Poly := [(pm0, (-4194304 : Int))]
def n0073Num : Poly := n0073NumPart0

def n0073NF : NF := ⟨n0073Num, (729 : Int)⟩

def n0073QPart0 : Poly := []
def n0073Q : Poly := n0073QPart0

def n0073Row : Row := ⟨n0073NF, .mul 11 72, (1 : Int), n0073Q⟩

def n0074NumPart0 : Poly := [(pm0, (4194304 : Int))]
def n0074Num : Poly := n0074NumPart0

def n0074NF : NF := ⟨n0074Num, (729 : Int)⟩

def n0074QPart0 : Poly := []
def n0074Q : Poly := n0074QPart0

def n0074Row : Row := ⟨n0074NF, .mul 4 73, (1 : Int), n0074Q⟩

def n0075NumPart0 : Poly := [(pm0, (-6509559808 : Int))]
def n0075Num : Poly := n0075NumPart0

def n0075NF : NF := ⟨n0075Num, (729 : Int)⟩

def n0075QPart0 : Poly := []
def n0075Q : Poly := n0075QPart0

def n0075Row : Row := ⟨n0075NF, .add 70 74, (1 : Int), n0075Q⟩

def n0076NumPart0 : Poly := [(pm0, (16384 : Int))]
def n0076Num : Poly := n0076NumPart0

def n0076NF : NF := ⟨n0076Num, (3 : Int)⟩

def n0076QPart0 : Poly := []
def n0076Q : Poly := n0076QPart0

def n0076Row : Row := ⟨n0076NF, .mul 5 7, (1 : Int), n0076Q⟩

def n0077NumPart0 : Poly := [(pm0, (27 : Int))]
def n0077Num : Poly := n0077NumPart0

def n0077NF : NF := ⟨n0077Num, (1 : Int)⟩

def n0077QPart0 : Poly := []
def n0077Q : Poly := n0077QPart0

def n0077Row : Row := ⟨n0077NF, .mul 1 16, (1 : Int), n0077Q⟩

def n0078NumPart0 : Poly := [(pm0, (147456 : Int))]
def n0078Num : Poly := n0078NumPart0

def n0078NF : NF := ⟨n0078Num, (1 : Int)⟩

def n0078QPart0 : Poly := []
def n0078Q : Poly := n0078QPart0

def n0078Row : Row := ⟨n0078NF, .mul 76 77, (1 : Int), n0078Q⟩

def n0079NumPart0 : Poly := [(pm0, (311296 : Int))]
def n0079Num : Poly := n0079NumPart0

def n0079NF : NF := ⟨n0079Num, (1 : Int)⟩

def n0079QPart0 : Poly := []
def n0079Q : Poly := n0079QPart0

def n0079Row : Row := ⟨n0079NF, .mul 3 78, (1 : Int), n0079Q⟩

def n0080NumPart0 : Poly := [(pm0, (-311296 : Int))]
def n0080Num : Poly := n0080NumPart0

def n0080NF : NF := ⟨n0080Num, (1 : Int)⟩

def n0080QPart0 : Poly := []
def n0080Q : Poly := n0080QPart0

def n0080Row : Row := ⟨n0080NF, .mul 4 79, (1 : Int), n0080Q⟩

def n0081NumPart0 : Poly := [(pm0, (-6736494592 : Int))]
def n0081Num : Poly := n0081NumPart0

def n0081NF : NF := ⟨n0081Num, (729 : Int)⟩

def n0081QPart0 : Poly := []
def n0081Q : Poly := n0081QPart0

def n0081Row : Row := ⟨n0081NF, .add 75 80, (1 : Int), n0081Q⟩

def n0082NumPart0 : Poly := [(pm0, (1600 : Int))]
def n0082Num : Poly := n0082NumPart0

def n0082NF : NF := ⟨n0082Num, (1 : Int)⟩

def n0082QPart0 : Poly := []
def n0082Q : Poly := n0082QPart0

def n0082Row : Row := ⟨n0082NF, .lit (1600 : Int) (1 : Int), (1 : Int), n0082Q⟩

def n0083NumPart0 : Poly := [(pm0, (6553600 : Int))]
def n0083Num : Poly := n0083NumPart0

def n0083NF : NF := ⟨n0083Num, (81 : Int)⟩

def n0083QPart0 : Poly := []
def n0083Q : Poly := n0083QPart0

def n0083Row : Row := ⟨n0083NF, .mul 7 82, (1 : Int), n0083Q⟩

def n0084NumPart0 : Poly := [(pm0, (6553600 : Int))]
def n0084Num : Poly := n0084NumPart0

def n0084NF : NF := ⟨n0084Num, (3 : Int)⟩

def n0084QPart0 : Poly := []
def n0084Q : Poly := n0084QPart0

def n0084Row : Row := ⟨n0084NF, .mul 77 83, (1 : Int), n0084Q⟩

def n0085NumPart0 : Poly := [(pm0, (-6553600 : Int))]
def n0085Num : Poly := n0085NumPart0

def n0085NF : NF := ⟨n0085Num, (3 : Int)⟩

def n0085QPart0 : Poly := []
def n0085Q : Poly := n0085QPart0

def n0085Row : Row := ⟨n0085NF, .mul 11 84, (1 : Int), n0085Q⟩

def n0086NumPart0 : Poly := [(pm0, (-8329019392 : Int))]
def n0086Num : Poly := n0086NumPart0

def n0086NF : NF := ⟨n0086Num, (729 : Int)⟩

def n0086QPart0 : Poly := []
def n0086Q : Poly := n0086QPart0

def n0086Row : Row := ⟨n0086NF, .add 81 85, (1 : Int), n0086Q⟩

def n0087NumPart0 : Poly := [(pm0, (144 : Int))]
def n0087Num : Poly := n0087NumPart0

def n0087NF : NF := ⟨n0087Num, (1 : Int)⟩

def n0087QPart0 : Poly := []
def n0087Q : Poly := n0087QPart0

def n0087Row : Row := ⟨n0087NF, .lit (144 : Int) (1 : Int), (1 : Int), n0087Q⟩

def n0088NumPart0 : Poly := [(pm0, (65536 : Int))]
def n0088Num : Poly := n0088NumPart0

def n0088NF : NF := ⟨n0088Num, (9 : Int)⟩

def n0088QPart0 : Poly := []
def n0088Q : Poly := n0088QPart0

def n0088Row : Row := ⟨n0088NF, .mul 7 87, (1 : Int), n0088Q⟩

def n0089NumPart0 : Poly := [(pm0, (196608 : Int))]
def n0089Num : Poly := n0089NumPart0

def n0089NF : NF := ⟨n0089Num, (1 : Int)⟩

def n0089QPart0 : Poly := []
def n0089Q : Poly := n0089QPart0

def n0089Row : Row := ⟨n0089NF, .mul 77 88, (1 : Int), n0089Q⟩

def n0090NumPart0 : Poly := [(pm0, (196608 : Int))]
def n0090Num : Poly := n0090NumPart0

def n0090NF : NF := ⟨n0090Num, (1 : Int)⟩

def n0090QPart0 : Poly := []
def n0090Q : Poly := n0090QPart0

def n0090Row : Row := ⟨n0090NF, .mul 10 89, (1 : Int), n0090Q⟩

def n0091NumPart0 : Poly := [(pm0, (-196608 : Int))]
def n0091Num : Poly := n0091NumPart0

def n0091NF : NF := ⟨n0091Num, (1 : Int)⟩

def n0091QPart0 : Poly := []
def n0091Q : Poly := n0091QPart0

def n0091Row : Row := ⟨n0091NF, .mul 4 90, (1 : Int), n0091Q⟩

def n0092NumPart0 : Poly := [(pm0, (-8472346624 : Int))]
def n0092Num : Poly := n0092NumPart0

def n0092NF : NF := ⟨n0092Num, (729 : Int)⟩

def n0092QPart0 : Poly := []
def n0092Q : Poly := n0092QPart0

def n0092Row : Row := ⟨n0092NF, .add 86 91, (1 : Int), n0092Q⟩

def n0093NumPart0 : Poly := [(pm0, (9720 : Int))]
def n0093Num : Poly := n0093NumPart0

def n0093NF : NF := ⟨n0093Num, (1 : Int)⟩

def n0093QPart0 : Poly := []
def n0093Q : Poly := n0093QPart0

def n0093Row : Row := ⟨n0093NF, .lit (9720 : Int) (1 : Int), (1 : Int), n0093Q⟩

def n0094NumPart0 : Poly := [(pm0, (491520 : Int))]
def n0094Num : Poly := n0094NumPart0

def n0094NF : NF := ⟨n0094Num, (1 : Int)⟩

def n0094QPart0 : Poly := []
def n0094Q : Poly := n0094QPart0

def n0094Row : Row := ⟨n0094NF, .mul 7 93, (1 : Int), n0094Q⟩

def n0095NumPart0 : Poly := [(pm0, (4423680 : Int))]
def n0095Num : Poly := n0095NumPart0

def n0095NF : NF := ⟨n0095Num, (1 : Int)⟩

def n0095QPart0 : Poly := []
def n0095Q : Poly := n0095QPart0

def n0095Row : Row := ⟨n0095NF, .mul 16 94, (1 : Int), n0095Q⟩

def n0096NumPart0 : Poly := [(pm0, (9338880 : Int))]
def n0096Num : Poly := n0096NumPart0

def n0096NF : NF := ⟨n0096Num, (1 : Int)⟩

def n0096QPart0 : Poly := []
def n0096Q : Poly := n0096QPart0

def n0096Row : Row := ⟨n0096NF, .mul 3 95, (1 : Int), n0096Q⟩

def n0097NumPart0 : Poly := [(pm0, (9338880 : Int))]
def n0097Num : Poly := n0097NumPart0

def n0097NF : NF := ⟨n0097Num, (1 : Int)⟩

def n0097QPart0 : Poly := []
def n0097Q : Poly := n0097QPart0

def n0097Row : Row := ⟨n0097NF, .mul 10 96, (1 : Int), n0097Q⟩

def n0098NumPart0 : Poly := [(pm0, (-1664303104 : Int))]
def n0098Num : Poly := n0098NumPart0

def n0098NF : NF := ⟨n0098Num, (729 : Int)⟩

def n0098QPart0 : Poly := []
def n0098Q : Poly := n0098QPart0

def n0098Row : Row := ⟨n0098NF, .add 92 97, (1 : Int), n0098Q⟩

def n0099NumPart0 : Poly := [(pm0, (2808 : Int))]
def n0099Num : Poly := n0099NumPart0

def n0099NF : NF := ⟨n0099Num, (1 : Int)⟩

def n0099QPart0 : Poly := []
def n0099Q : Poly := n0099QPart0

def n0099Row : Row := ⟨n0099NF, .lit (2808 : Int) (1 : Int), (1 : Int), n0099Q⟩

def n0100NumPart0 : Poly := [(pm0, (425984 : Int))]
def n0100Num : Poly := n0100NumPart0

def n0100NF : NF := ⟨n0100Num, (3 : Int)⟩

def n0100QPart0 : Poly := []
def n0100Q : Poly := n0100QPart0

def n0100Row : Row := ⟨n0100NF, .mul 7 99, (1 : Int), n0100Q⟩

def n0101NumPart0 : Poly := [(pm0, (1277952 : Int))]
def n0101Num : Poly := n0101NumPart0

def n0101NF : NF := ⟨n0101Num, (1 : Int)⟩

def n0101QPart0 : Poly := []
def n0101Q : Poly := n0101QPart0

def n0101Row : Row := ⟨n0101NF, .mul 16 100, (1 : Int), n0101Q⟩

def n0102NumPart0 : Poly := [(pm0, (8093696 : Int))]
def n0102Num : Poly := n0102NumPart0

def n0102NF : NF := ⟨n0102Num, (3 : Int)⟩

def n0102QPart0 : Poly := []
def n0102Q : Poly := n0102QPart0

def n0102Row : Row := ⟨n0102NF, .mul 3 101, (1 : Int), n0102Q⟩

def n0103NumPart0 : Poly := [(pm0, (-8093696 : Int))]
def n0103Num : Poly := n0103NumPart0

def n0103NF : NF := ⟨n0103Num, (3 : Int)⟩

def n0103QPart0 : Poly := []
def n0103Q : Poly := n0103QPart0

def n0103Row : Row := ⟨n0103NF, .mul 2 102, (1 : Int), n0103Q⟩

def n0104NumPart0 : Poly := [(pm0, (8093696 : Int))]
def n0104Num : Poly := n0104NumPart0

def n0104NF : NF := ⟨n0104Num, (3 : Int)⟩

def n0104QPart0 : Poly := []
def n0104Q : Poly := n0104QPart0

def n0104Row : Row := ⟨n0104NF, .mul 4 103, (1 : Int), n0104Q⟩

def n0105NumPart0 : Poly := [(pm0, (302465024 : Int))]
def n0105Num : Poly := n0105NumPart0

def n0105NF : NF := ⟨n0105Num, (729 : Int)⟩

def n0105QPart0 : Poly := []
def n0105Q : Poly := n0105QPart0

def n0105Row : Row := ⟨n0105NF, .add 98 104, (1 : Int), n0105Q⟩

def n0106NumPart0 : Poly := [(pm0, (2000 : Int))]
def n0106Num : Poly := n0106NumPart0

def n0106NF : NF := ⟨n0106Num, (1 : Int)⟩

def n0106QPart0 : Poly := []
def n0106Q : Poly := n0106QPart0

def n0106Row : Row := ⟨n0106NF, .lit (2000 : Int) (1 : Int), (1 : Int), n0106Q⟩

def n0107NumPart0 : Poly := [(pm0, (8192000 : Int))]
def n0107Num : Poly := n0107NumPart0

def n0107NF : NF := ⟨n0107Num, (81 : Int)⟩

def n0107QPart0 : Poly := []
def n0107Q : Poly := n0107QPart0

def n0107Row : Row := ⟨n0107NF, .mul 7 106, (1 : Int), n0107Q⟩

def n0108NumPart0 : Poly := [(pm0, (8192000 : Int))]
def n0108Num : Poly := n0108NumPart0

def n0108NF : NF := ⟨n0108Num, (9 : Int)⟩

def n0108QPart0 : Poly := []
def n0108Q : Poly := n0108QPart0

def n0108Row : Row := ⟨n0108NF, .mul 16 107, (1 : Int), n0108Q⟩

def n0109NumPart0 : Poly := [(pm0, (8192000 : Int))]
def n0109Num : Poly := n0109NumPart0

def n0109NF : NF := ⟨n0109Num, (9 : Int)⟩

def n0109QPart0 : Poly := []
def n0109Q : Poly := n0109QPart0

def n0109Row : Row := ⟨n0109NF, .mul 29 108, (1 : Int), n0109Q⟩

def n0110NumPart0 : Poly := [(pm0, (-8192000 : Int))]
def n0110Num : Poly := n0110NumPart0

def n0110NF : NF := ⟨n0110Num, (9 : Int)⟩

def n0110QPart0 : Poly := []
def n0110Q : Poly := n0110QPart0

def n0110Row : Row := ⟨n0110NF, .mul 4 109, (1 : Int), n0110Q⟩

def n0111NumPart0 : Poly := [(pm0, (-361086976 : Int))]
def n0111Num : Poly := n0111NumPart0

def n0111NF : NF := ⟨n0111Num, (729 : Int)⟩

def n0111QPart0 : Poly := []
def n0111Q : Poly := n0111QPart0

def n0111Row : Row := ⟨n0111NF, .add 105 110, (1 : Int), n0111Q⟩

def n0112NumPart0 : Poly := [(pm0, (560 : Int))]
def n0112Num : Poly := n0112NumPart0

def n0112NF : NF := ⟨n0112Num, (1 : Int)⟩

def n0112QPart0 : Poly := []
def n0112Q : Poly := n0112QPart0

def n0112Row : Row := ⟨n0112NF, .lit (560 : Int) (1 : Int), (1 : Int), n0112Q⟩

def n0113NumPart0 : Poly := [(pm0, (2293760 : Int))]
def n0113Num : Poly := n0113NumPart0

def n0113NF : NF := ⟨n0113Num, (81 : Int)⟩

def n0113QPart0 : Poly := []
def n0113Q : Poly := n0113QPart0

def n0113Row : Row := ⟨n0113NF, .mul 7 112, (1 : Int), n0113Q⟩

def n0114NumPart0 : Poly := [(pm0, (2293760 : Int))]
def n0114Num : Poly := n0114NumPart0

def n0114NF : NF := ⟨n0114Num, (9 : Int)⟩

def n0114QPart0 : Poly := []
def n0114Q : Poly := n0114QPart0

def n0114Row : Row := ⟨n0114NF, .mul 16 113, (1 : Int), n0114Q⟩

def n0115NumPart0 : Poly := [(pm0, (-2293760 : Int))]
def n0115Num : Poly := n0115NumPart0

def n0115NF : NF := ⟨n0115Num, (9 : Int)⟩

def n0115QPart0 : Poly := []
def n0115Q : Poly := n0115QPart0

def n0115Row : Row := ⟨n0115NF, .mul 11 114, (1 : Int), n0115Q⟩

def n0116NumPart0 : Poly := [(pm0, (2293760 : Int))]
def n0116Num : Poly := n0116NumPart0

def n0116NF : NF := ⟨n0116Num, (9 : Int)⟩

def n0116QPart0 : Poly := []
def n0116Q : Poly := n0116QPart0

def n0116Row : Row := ⟨n0116NF, .mul 4 115, (1 : Int), n0116Q⟩

def n0117NumPart0 : Poly := [(pm0, (-175292416 : Int))]
def n0117Num : Poly := n0117NumPart0

def n0117NF : NF := ⟨n0117Num, (729 : Int)⟩

def n0117QPart0 : Poly := []
def n0117Q : Poly := n0117QPart0

def n0117Row : Row := ⟨n0117NF, .add 111 116, (1 : Int), n0117Q⟩

def n0118NumPart0 : Poly := [(pm0, (4 : Int))]
def n0118Num : Poly := n0118NumPart0

def n0118NF : NF := ⟨n0118Num, (1 : Int)⟩

def n0118QPart0 : Poly := []
def n0118Q : Poly := n0118QPart0

def n0118Row : Row := ⟨n0118NF, .lit (4 : Int) (1 : Int), (1 : Int), n0118Q⟩

def n0119NumPart0 : Poly := [(pm0, (16384 : Int))]
def n0119Num : Poly := n0119NumPart0

def n0119NF : NF := ⟨n0119Num, (81 : Int)⟩

def n0119QPart0 : Poly := []
def n0119Q : Poly := n0119QPart0

def n0119Row : Row := ⟨n0119NF, .mul 7 118, (1 : Int), n0119Q⟩

def n0120NumPart0 : Poly := [(pm0, (16384 : Int))]
def n0120Num : Poly := n0120NumPart0

def n0120NF : NF := ⟨n0120Num, (9 : Int)⟩

def n0120QPart0 : Poly := []
def n0120Q : Poly := n0120QPart0

def n0120Row : Row := ⟨n0120NF, .mul 16 119, (1 : Int), n0120Q⟩

def n0121NumPart0 : Poly := [(pm0, (16384 : Int))]
def n0121Num : Poly := n0121NumPart0

def n0121NF : NF := ⟨n0121Num, (9 : Int)⟩

def n0121QPart0 : Poly := []
def n0121Q : Poly := n0121QPart0

def n0121Row : Row := ⟨n0121NF, .mul 10 120, (1 : Int), n0121Q⟩

def n0122NumPart0 : Poly := [(pm0, (-173965312 : Int))]
def n0122Num : Poly := n0122NumPart0

def n0122NF : NF := ⟨n0122Num, (729 : Int)⟩

def n0122QPart0 : Poly := []
def n0122Q : Poly := n0122QPart0

def n0122Row : Row := ⟨n0122NF, .add 117 121, (1 : Int), n0122Q⟩

def n0123NumPart0 : Poly := [(pm0, (21384 : Int))]
def n0123Num : Poly := n0123NumPart0

def n0123NF : NF := ⟨n0123Num, (1 : Int)⟩

def n0123QPart0 : Poly := []
def n0123Q : Poly := n0123QPart0

def n0123Row : Row := ⟨n0123NF, .lit (21384 : Int) (1 : Int), (1 : Int), n0123Q⟩

def n0124NumPart0 : Poly := [(pm0, (1081344 : Int))]
def n0124Num : Poly := n0124NumPart0

def n0124NF : NF := ⟨n0124Num, (1 : Int)⟩

def n0124QPart0 : Poly := []
def n0124Q : Poly := n0124QPart0

def n0124Row : Row := ⟨n0124NF, .mul 7 123, (1 : Int), n0124Q⟩

def n0125NumPart0 : Poly := [(pm0, (3244032 : Int))]
def n0125Num : Poly := n0125NumPart0

def n0125NF : NF := ⟨n0125Num, (1 : Int)⟩

def n0125QPart0 : Poly := []
def n0125Q : Poly := n0125QPart0

def n0125Row : Row := ⟨n0125NF, .mul 1 124, (1 : Int), n0125Q⟩

def n0126NumPart0 : Poly := [(pm0, (130121728 : Int))]
def n0126Num : Poly := n0126NumPart0

def n0126NF : NF := ⟨n0126Num, (9 : Int)⟩

def n0126QPart0 : Poly := []
def n0126Q : Poly := n0126QPart0

def n0126Row : Row := ⟨n0126NF, .mul 40 125, (1 : Int), n0126Q⟩

def n0127NumPart0 : Poly := [(pm0, (-130121728 : Int))]
def n0127Num : Poly := n0127NumPart0

def n0127NF : NF := ⟨n0127Num, (9 : Int)⟩

def n0127QPart0 : Poly := []
def n0127Q : Poly := n0127QPart0

def n0127Row : Row := ⟨n0127NF, .mul 2 126, (1 : Int), n0127Q⟩

end N6.BranchEval.B0.ProgramData
