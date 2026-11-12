import N6.BranchEval.ProgramCore
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
namespace N6.Even.ProgramData
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

def factorDataPart0 : Poly := [(pm0, (-27 : Int)), (pm1, (378 : Int)), (pm2, (-1821 : Int)), (pm3, (3324 : Int)), (pm4, (-1605 : Int)), (pm5, (650 : Int)), (pm6, (125 : Int))]
def factorData : Poly := factorDataPart0

def input0NumPart0 : Poly := [(pm1, (1 : Int))]
def input0Num : Poly := input0NumPart0

def input0NF : NF := ⟨input0Num,(1 : Int)⟩
def input1NumPart0 : Poly := [(pm0, (207 : Int)), (pm1, (-2013 : Int)), (pm2, (5376 : Int)), (pm3, (-2584 : Int)), (pm4, (1225 : Int)), (pm5, (225 : Int))]
def input1Num : Poly := input1NumPart0

def input1NF : NF := ⟨input1Num,(180 : Int)⟩
def input2NumPart0 : Poly := [(pm0, (-541508040364032 : Int)), (pm1, (7661439640977408 : Int)), (pm2, (-37654574059954176 : Int)), (pm3, (72199065264881664 : Int)), (pm4, (-42636182059929600 : Int)), (pm5, (18838912298598400 : Int))]
def input2Num : Poly := input2NumPart0

def input2NF : NF := ⟨input2Num,(889892578125 : Int)⟩
def input3NumPart0 : Poly := [(pm0, (-555271483392 : Int)), (pm1, (7887409717248 : Int)), (pm2, (-39056291782656 : Int)), (pm3, (76231909392384 : Int)), (pm4, (-47896999833600 : Int)), (pm5, (21317073510400 : Int))]
def input3Num : Poly := input3NumPart0

def input3NF : NF := ⟨input3Num,(158203125 : Int)⟩
def input4NumPart0 : Poly := [(pm0, (27977121792 : Int)), (pm1, (-393245134848 : Int)), (pm2, (1909608185856 : Int)), (pm3, (-3561511133184 : Int)), (pm4, (1916795289600 : Int)), (pm5, (-897476710400 : Int))]
def input4Num : Poly := input4NumPart0

def input4NF : NF := ⟨input4Num,(140625 : Int)⟩
def input5NumPart0 : Poly := [(pm0, (-3146067 : Int)), (pm1, (30206310 : Int)), (pm2, (-78098226 : Int)), (pm3, (37868220 : Int)), (pm4, (-17607475 : Int)), (pm5, (-3249250 : Int))]
def input5Num : Poly := input5NumPart0

def input5NF : NF := ⟨input5Num,(200 : Int)⟩
def input6NumPart0 : Poly := [(pm0, (-54217579843964399638960334682497485872562176 : Int)), (pm1, (518404997007633475346979149913903171140321280 : Int)), (pm2, (-1349682106430269325291105001999212728578736128 : Int)), (pm3, (627227208715985549448906731198284178820956160 : Int)), (pm4, (-296820281236716747008826173836284255849676800 : Int)), (pm5, (-54658869202062559901334974258930729877504000 : Int))]
def input6Num : Poly := input6NumPart0

def input6NF : NF := ⟨input6Num,(88817841970012523233890533447265625 : Int)⟩
def n000NumPart0 : Poly := [(pm1, (1 : Int))]
def n000Num : Poly := n000NumPart0

def n000NF : NF := ⟨n000Num,(1 : Int)⟩
def n000QPart0 : Poly := []
def n000Q : Poly := n000QPart0

def n000Row : Row := ⟨n000NF,.input 0,(1 : Int),n000Q⟩

def n001NumPart0 : Poly := [(pm0, (207 : Int)), (pm1, (-2013 : Int)), (pm2, (5376 : Int)), (pm3, (-2584 : Int)), (pm4, (1225 : Int)), (pm5, (225 : Int))]
def n001Num : Poly := n001NumPart0

def n001NF : NF := ⟨n001Num,(180 : Int)⟩
def n001QPart0 : Poly := []
def n001Q : Poly := n001QPart0

def n001Row : Row := ⟨n001NF,.input 1,(1 : Int),n001Q⟩

def n002NumPart0 : Poly := [(pm0, (1024 : Int))]
def n002Num : Poly := n002NumPart0

def n002NF : NF := ⟨n002Num,(1 : Int)⟩
def n002QPart0 : Poly := []
def n002Q : Poly := n002QPart0

def n002Row : Row := ⟨n002NF,.lit (1024 : Int) (1 : Int),(1 : Int),n002Q⟩

def n003NumPart0 : Poly := [(pm2, (1 : Int))]
def n003Num : Poly := n003NumPart0

def n003NF : NF := ⟨n003Num,(1 : Int)⟩
def n003QPart0 : Poly := []
def n003Q : Poly := n003QPart0

def n003Row : Row := ⟨n003NF,.mul 0 0,(1 : Int),n003Q⟩

def n004NumPart0 : Poly := [(pm3, (1 : Int))]
def n004Num : Poly := n004NumPart0

def n004NF : NF := ⟨n004Num,(1 : Int)⟩
def n004QPart0 : Poly := []
def n004Q : Poly := n004QPart0

def n004Row : Row := ⟨n004NF,.mul 0 3,(1 : Int),n004Q⟩

def n005NumPart0 : Poly := [(pm0, (27 : Int)), (pm1, (-378 : Int)), (pm2, (1821 : Int)), (pm3, (-3324 : Int)), (pm4, (1605 : Int)), (pm5, (-650 : Int))]
def n005Num : Poly := n005NumPart0

def n005NF : NF := ⟨n005Num,(125 : Int)⟩
def n005QPart0 : Poly := [(pm0, (1 : Int))]
def n005Q : Poly := n005QPart0

def n005Row : Row := ⟨n005NF,.mul 4 4,(1 : Int),n005Q⟩

def n006NumPart0 : Poly := [(pm0, (27648 : Int)), (pm1, (-387072 : Int)), (pm2, (1864704 : Int)), (pm3, (-3403776 : Int)), (pm4, (1643520 : Int)), (pm5, (-665600 : Int))]
def n006Num : Poly := n006NumPart0

def n006NF : NF := ⟨n006Num,(125 : Int)⟩
def n006QPart0 : Poly := []
def n006Q : Poly := n006QPart0

def n006Row : Row := ⟨n006NF,.mul 2 5,(1 : Int),n006Q⟩

def n007NumPart0 : Poly := [(pm0, (-353956608 : Int)), (pm1, (4994410752 : Int)), (pm2, (-24418489344 : Int)), (pm3, (46221551616 : Int)), (pm4, (-26014982400 : Int)), (pm5, (11455609600 : Int))]
def n007Num : Poly := n007NumPart0

def n007NF : NF := ⟨n007Num,(703125 : Int)⟩
def n007QPart0 : Poly := [(pm0, (-444003840000 : Int)), (pm1, (1481875200000 : Int)), (pm2, (-3870576000000 : Int)), (pm3, (1874160000000 : Int)), (pm4, (-842400000000 : Int))]
def n007Q : Poly := n007QPart0

def n007Row : Row := ⟨n007NF,.mul 1 6,(1 : Int),n007Q⟩

def n008NumPart0 : Poly := [(pm0, (512 : Int))]
def n008Num : Poly := n008NumPart0

def n008NF : NF := ⟨n008Num,(1 : Int)⟩
def n008QPart0 : Poly := []
def n008Q : Poly := n008QPart0

def n008Row : Row := ⟨n008NF,.lit (512 : Int) (1 : Int),(1 : Int),n008Q⟩

def n009NumPart0 : Poly := [(pm4, (1 : Int))]
def n009Num : Poly := n009NumPart0

def n009NF : NF := ⟨n009Num,(1 : Int)⟩
def n009QPart0 : Poly := []
def n009Q : Poly := n009QPart0

def n009Row : Row := ⟨n009NF,.mul 3 3,(1 : Int),n009Q⟩

def n010NumPart0 : Poly := [(pm5, (1 : Int))]
def n010Num : Poly := n010NumPart0

def n010NF : NF := ⟨n010Num,(1 : Int)⟩
def n010QPart0 : Poly := []
def n010Q : Poly := n010QPart0

def n010Row : Row := ⟨n010NF,.mul 0 9,(1 : Int),n010Q⟩

def n011NumPart0 : Poly := [(pm5, (512 : Int))]
def n011Num : Poly := n011NumPart0

def n011NF : NF := ⟨n011Num,(1 : Int)⟩
def n011QPart0 : Poly := []
def n011Q : Poly := n011QPart0

def n011Row : Row := ⟨n011NF,.mul 8 10,(1 : Int),n011Q⟩

def n012NumPart0 : Poly := [(pm0, (3901824 : Int)), (pm1, (-54608256 : Int)), (pm2, (264556032 : Int)), (pm3, (-497422848 : Int)), (pm4, (293443200 : Int)), (pm5, (-163868800 : Int))]
def n012Num : Poly := n012NumPart0

def n012NF : NF := ⟨n012Num,(140625 : Int)⟩
def n012QPart0 : Poly := [(pm0, (26012160 : Int)), (pm1, (115200 : Int)), (pm2, (10944000 : Int)), (pm3, (31680000 : Int)), (pm4, (129600000 : Int))]
def n012Q : Poly := n012QPart0

def n012Row : Row := ⟨n012NF,.mul 1 11,(1 : Int),n012Q⟩

def n013NumPart0 : Poly := [(pm0, (-1 : Int))]
def n013Num : Poly := n013NumPart0

def n013NF : NF := ⟨n013Num,(1 : Int)⟩
def n013QPart0 : Poly := []
def n013Q : Poly := n013QPart0

def n013Row : Row := ⟨n013NF,.lit (-1 : Int) (1 : Int),(1 : Int),n013Q⟩

def n014NumPart0 : Poly := [(pm0, (-3901824 : Int)), (pm1, (54608256 : Int)), (pm2, (-264556032 : Int)), (pm3, (497422848 : Int)), (pm4, (-293443200 : Int)), (pm5, (163868800 : Int))]
def n014Num : Poly := n014NumPart0

def n014NF : NF := ⟨n014Num,(140625 : Int)⟩
def n014QPart0 : Poly := []
def n014Q : Poly := n014QPart0

def n014Row : Row := ⟨n014NF,.mul 12 13,(1 : Int),n014Q⟩

def n015NumPart0 : Poly := [(pm0, (-124488576 : Int)), (pm1, (1755817344 : Int)), (pm2, (-8580423168 : Int)), (pm3, (16236221952 : Int)), (pm4, (-9160732800 : Int)), (pm5, (4091651200 : Int))]
def n015Num : Poly := n015NumPart0

def n015NF : NF := ⟨n015Num,(234375 : Int)⟩
def n015QPart0 : Poly := []
def n015Q : Poly := n015QPart0

def n015Row : Row := ⟨n015NF,.add 7 14,(1 : Int),n015Q⟩

def n016NumPart0 : Poly := [(pm0, (9216 : Int))]
def n016Num : Poly := n016NumPart0

def n016NF : NF := ⟨n016Num,(1 : Int)⟩
def n016QPart0 : Poly := []
def n016Q : Poly := n016QPart0

def n016Row : Row := ⟨n016NF,.lit (9216 : Int) (1 : Int),(1 : Int),n016Q⟩

def n017NumPart0 : Poly := [(pm4, (9216 : Int))]
def n017Num : Poly := n017NumPart0

def n017NF : NF := ⟨n017Num,(1 : Int)⟩
def n017QPart0 : Poly := []
def n017Q : Poly := n017QPart0

def n017Row : Row := ⟨n017NF,.mul 9 16,(1 : Int),n017Q⟩

def n018NumPart0 : Poly := [(pm0, (1647 : Int)), (pm1, (-16443 : Int)), (pm2, (46146 : Int)), (pm3, (-27444 : Int)), (pm4, (10425 : Int)), (pm5, (1975 : Int))]
def n018Num : Poly := n018NumPart0

def n018NF : NF := ⟨n018Num,(101250 : Int)⟩
def n018QPart0 : Poly := [(pm0, (-158707350 : Int)), (pm1, (883548000 : Int)), (pm2, (-412897500 : Int)), (pm3, (233280000 : Int)), (pm4, (41006250 : Int))]
def n018Q : Poly := n018QPart0

def n018Row : Row := ⟨n018NF,.mul 1 1,(1 : Int),n018Q⟩

def n019NumPart0 : Poly := [(pm0, (736141824 : Int)), (pm1, (-10505811456 : Int)), (pm2, (52456952832 : Int)), (pm3, (-104117864448 : Int)), (pm4, (67698777600 : Int)), (pm5, (-26974220800 : Int))]
def n019Num : Poly := n019NumPart0

def n019NF : NF := ⟨n019Num,(3515625 : Int)⟩
def n019QPart0 : Poly := [(pm0, (2760531840000 : Int)), (pm1, (-749347200000 : Int)), (pm2, (40176000000 : Int)), (pm3, (511920000000 : Int))]
def n019Q : Poly := n019QPart0

def n019Row : Row := ⟨n019NF,.mul 17 18,(1 : Int),n019Q⟩

def n020NumPart0 : Poly := [(pm0, (-736141824 : Int)), (pm1, (10505811456 : Int)), (pm2, (-52456952832 : Int)), (pm3, (104117864448 : Int)), (pm4, (-67698777600 : Int)), (pm5, (26974220800 : Int))]
def n020Num : Poly := n020NumPart0

def n020NF : NF := ⟨n020Num,(3515625 : Int)⟩
def n020QPart0 : Poly := []
def n020Q : Poly := n020QPart0

def n020Row : Row := ⟨n020NF,.mul 13 19,(1 : Int),n020Q⟩

def n021NumPart0 : Poly := [(pm0, (-2603470464 : Int)), (pm1, (36843071616 : Int)), (pm2, (-181163300352 : Int)), (pm3, (347661193728 : Int)), (pm4, (-205109769600 : Int)), (pm5, (88348988800 : Int))]
def n021Num : Poly := n021NumPart0

def n021NF : NF := ⟨n021Num,(3515625 : Int)⟩
def n021QPart0 : Poly := []
def n021Q : Poly := n021QPart0

def n021Row : Row := ⟨n021NF,.add 15 20,(1 : Int),n021Q⟩

def n022NumPart0 : Poly := [(pm0, (64 : Int))]
def n022Num : Poly := n022NumPart0

def n022NF : NF := ⟨n022Num,(1 : Int)⟩
def n022QPart0 : Poly := []
def n022Q : Poly := n022QPart0

def n022Row : Row := ⟨n022NF,.lit (64 : Int) (1 : Int),(1 : Int),n022Q⟩

def n023NumPart0 : Poly := [(pm4, (64 : Int))]
def n023Num : Poly := n023NumPart0

def n023NF : NF := ⟨n023Num,(1 : Int)⟩
def n023QPart0 : Poly := []
def n023Q : Poly := n023QPart0

def n023Row : Row := ⟨n023NF,.mul 9 22,(1 : Int),n023Q⟩

def n024NumPart0 : Poly := [(pm0, (432 : Int)), (pm1, (34992 : Int)), (pm2, (-426624 : Int)), (pm3, (1537536 : Int)), (pm4, (-1748400 : Int)), (pm5, (451600 : Int))]
def n024Num : Poly := n024NumPart0

def n024NF : NF := ⟨n024Num,(28125 : Int)⟩
def n024QPart0 : Poly := [(pm0, (2880 : Int)), (pm1, (273600 : Int)), (pm2, (792000 : Int)), (pm3, (3240000 : Int))]
def n024Q : Poly := n024QPart0

def n024Row : Row := ⟨n024NF,.mul 1 23,(1 : Int),n024Q⟩

def n025NumPart0 : Poly := [(pm0, (-867805488 : Int)), (pm1, (12282481872 : Int)), (pm2, (-60405542784 : Int)), (pm3, (115951128576 : Int)), (pm4, (-68442773200 : Int)), (pm5, (29468479600 : Int))]
def n025Num : Poly := n025NumPart0

def n025NF : NF := ⟨n025Num,(1171875 : Int)⟩
def n025QPart0 : Poly := []
def n025Q : Poly := n025QPart0

def n025Row : Row := ⟨n025NF,.add 21 24,(1 : Int),n025Q⟩

def n026NumPart0 : Poly := [(pm0, (13824 : Int))]
def n026Num : Poly := n026NumPart0

def n026NF : NF := ⟨n026Num,(1 : Int)⟩
def n026QPart0 : Poly := []
def n026Q : Poly := n026QPart0

def n026Row : Row := ⟨n026NF,.lit (13824 : Int) (1 : Int),(1 : Int),n026Q⟩

def n027NumPart0 : Poly := [(pm3, (13824 : Int))]
def n027Num : Poly := n027NumPart0

def n027NF : NF := ⟨n027Num,(1 : Int)⟩
def n027QPart0 : Poly := []
def n027Q : Poly := n027QPart0

def n027Row : Row := ⟨n027NF,.mul 4 26,(1 : Int),n027Q⟩

def n028NumPart0 : Poly := [(pm0, (-36261 : Int)), (pm1, (675459 : Int)), (pm2, (-3980148 : Int)), (pm3, (7726872 : Int)), (pm4, (-885375 : Int)), (pm5, (-10175 : Int))]
def n028Num : Poly := n028NumPart0

def n028NF : NF := ⟨n028Num,(227812500 : Int)⟩
def n028QPart0 : Poly := [(pm0, (-2901064612500 : Int)), (pm1, (16533537750000 : Int)), (pm2, (-10140390000000 : Int)), (pm3, (4472870625000 : Int)), (pm4, (809873437500 : Int))]
def n028Q : Poly := n028QPart0

def n028Row : Row := ⟨n028NF,.mul 1 18,(1 : Int),n028Q⟩

def n029NumPart0 : Poly := [(pm0, (41212948608 : Int)), (pm1, (-579858279552 : Int)), (pm2, (2819827244544 : Int)), (pm3, (-5267897366016 : Int)), (pm4, (2812507056000 : Int)), (pm5, (-1222538377600 : Int))]
def n029Num : Poly := n029NumPart0

def n029NF : NF := ⟨n029Num,(263671875 : Int)⟩
def n029QPart0 : Poly := [(pm0, (347734253880000000 : Int)), (pm1, (-24274679400000000 : Int)), (pm2, (-296703000000000 : Int))]
def n029Q : Poly := n029QPart0

def n029Row : Row := ⟨n029NF,.mul 27 28,(1 : Int),n029Q⟩

def n030NumPart0 : Poly := [(pm0, (-154043286192 : Int)), (pm1, (2183700141648 : Int)), (pm2, (-10771419881856 : Int)), (pm3, (20821106563584 : Int)), (pm4, (-12587116914000 : Int)), (pm5, (5407869532400 : Int))]
def n030Num : Poly := n030NumPart0

def n030NF : NF := ⟨n030Num,(263671875 : Int)⟩
def n030QPart0 : Poly := []
def n030Q : Poly := n030QPart0

def n030Row : Row := ⟨n030NF,.add 25 29,(1 : Int),n030Q⟩

def n031NumPart0 : Poly := [(pm0, (4352 : Int))]
def n031Num : Poly := n031NumPart0

def n031NF : NF := ⟨n031Num,(1 : Int)⟩
def n031QPart0 : Poly := []
def n031Q : Poly := n031QPart0

def n031Row : Row := ⟨n031NF,.lit (4352 : Int) (1 : Int),(1 : Int),n031Q⟩

def n032NumPart0 : Poly := [(pm3, (4352 : Int))]
def n032Num : Poly := n032NumPart0

def n032NF : NF := ⟨n032Num,(1 : Int)⟩
def n032QPart0 : Poly := []
def n032Q : Poly := n032QPart0

def n032Row : Row := ⟨n032NF,.mul 4 31,(1 : Int),n032Q⟩

def n033NumPart0 : Poly := [(pm0, (-169852032 : Int)), (pm1, (2387035008 : Int)), (pm2, (-11467032576 : Int)), (pm3, (20348350464 : Int)), (pm4, (-7864444800 : Int)), (pm5, (2896854400 : Int))]
def n033Num : Poly := n033NumPart0

def n033NF : NF := ⟨n033Num,(6328125 : Int)⟩
def n033QPart0 : Poly := [(pm0, (-636945120000 : Int)), (pm1, (34149600000 : Int)), (pm2, (435132000000 : Int))]
def n033Q : Poly := n033QPart0

def n033Row : Row := ⟨n033NF,.mul 18 32,(1 : Int),n033Q⟩

def n034NumPart0 : Poly := [(pm0, (-483361362576 : Int)), (pm1, (6849479800944 : Int)), (pm2, (-33747638717568 : Int)), (pm3, (65006863498752 : Int)), (pm4, (-38744406342000 : Int)), (pm5, (16585715397200 : Int))]
def n034Num : Poly := n034NumPart0

def n034NF : NF := ⟨n034Num,(791015625 : Int)⟩
def n034QPart0 : Poly := []
def n034Q : Poly := n034QPart0

def n034Row : Row := ⟨n034NF,.add 30 33,(1 : Int),n034Q⟩

def n035NumPart0 : Poly := [(pm0, (17280 : Int))]
def n035Num : Poly := n035NumPart0

def n035NF : NF := ⟨n035Num,(1 : Int)⟩
def n035QPart0 : Poly := []
def n035Q : Poly := n035QPart0

def n035Row : Row := ⟨n035NF,.lit (17280 : Int) (1 : Int),(1 : Int),n035Q⟩

def n036NumPart0 : Poly := [(pm2, (17280 : Int))]
def n036Num : Poly := n036NumPart0

def n036NF : NF := ⟨n036Num,(1 : Int)⟩
def n036QPart0 : Poly := []
def n036Q : Poly := n036QPart0

def n036Row : Row := ⟨n036NF,.mul 3 35,(1 : Int),n036Q⟩

def n037NumPart0 : Poly := [(pm0, (-143849952 : Int)), (pm1, (2012141088 : Int)), (pm2, (-9706273536 : Int)), (pm3, (18131311104 : Int)), (pm4, (-11518740000 : Int)), (pm5, (9540034400 : Int))]
def n037Num : Poly := n037NumPart0

def n037NF : NF := ⟨n037Num,(10546875 : Int)⟩
def n037QPart0 : Poly := [(pm0, (-1213733970000000 : Int)), (pm1, (-14835150000000 : Int))]
def n037Q : Poly := n037QPart0

def n037Row : Row := ⟨n037NF,.mul 28 36,(1 : Int),n037Q⟩

def n038NumPart0 : Poly := [(pm0, (-494150108976 : Int)), (pm1, (7000390382544 : Int)), (pm2, (-34475609232768 : Int)), (pm3, (66366711831552 : Int)), (pm4, (-39608311842000 : Int)), (pm5, (17301217977200 : Int))]
def n038Num : Poly := n038NumPart0

def n038NF : NF := ⟨n038Num,(791015625 : Int)⟩
def n038QPart0 : Poly := []
def n038Q : Poly := n038QPart0

def n038Row : Row := ⟨n038NF,.add 34 37,(1 : Int),n038Q⟩

def n039NumPart0 : Poly := [(pm2, (512 : Int))]
def n039Num : Poly := n039NumPart0

def n039NF : NF := ⟨n039Num,(1 : Int)⟩
def n039QPart0 : Poly := []
def n039Q : Poly := n039QPart0

def n039Row : Row := ⟨n039NF,.mul 3 8,(1 : Int),n039Q⟩

def n040NumPart0 : Poly := [(pm0, (214272 : Int)), (pm1, (-269568 : Int)), (pm2, (-13231104 : Int)), (pm3, (52525056 : Int)), (pm4, (-28051200 : Int)), (pm5, (-18502400 : Int))]
def n040Num : Poly := n040NumPart0

def n040NF : NF := ⟨n040Num,(1265625 : Int)⟩
def n040QPart0 : Poly := [(pm0, (803520000 : Int)), (pm1, (10238400000 : Int))]
def n040Q : Poly := n040QPart0

def n040Row : Row := ⟨n040NF,.mul 18 39,(1 : Int),n040Q⟩

def n041NumPart0 : Poly := [(pm0, (-214272 : Int)), (pm1, (269568 : Int)), (pm2, (13231104 : Int)), (pm3, (-52525056 : Int)), (pm4, (28051200 : Int)), (pm5, (18502400 : Int))]
def n041Num : Poly := n041NumPart0

def n041NF : NF := ⟨n041Num,(1265625 : Int)⟩
def n041QPart0 : Poly := []
def n041Q : Poly := n041QPart0

def n041Row : Row := ⟨n041NF,.mul 13 40,(1 : Int),n041Q⟩

def n042NumPart0 : Poly := [(pm0, (-494284028976 : Int)), (pm1, (7000558862544 : Int)), (pm2, (-34467339792768 : Int)), (pm3, (66333883671552 : Int)), (pm4, (-39590779842000 : Int)), (pm5, (17312781977200 : Int))]
def n042Num : Poly := n042NumPart0

def n042NF : NF := ⟨n042Num,(791015625 : Int)⟩
def n042QPart0 : Poly := []
def n042Q : Poly := n042QPart0

def n042Row : Row := ⟨n042NF,.add 38 41,(1 : Int),n042Q⟩

def n043NumPart0 : Poly := [(pm0, (62208 : Int))]
def n043Num : Poly := n043NumPart0

def n043NF : NF := ⟨n043Num,(1 : Int)⟩
def n043QPart0 : Poly := []
def n043Q : Poly := n043QPart0

def n043Row : Row := ⟨n043NF,.lit (62208 : Int) (1 : Int),(1 : Int),n043Q⟩

def n044NumPart0 : Poly := [(pm1, (62208 : Int))]
def n044Num : Poly := n044NumPart0

def n044NF : NF := ⟨n044Num,(1 : Int)⟩
def n044QPart0 : Poly := []
def n044Q : Poly := n044QPart0

def n044Row : Row := ⟨n044NF,.mul 0 43,(1 : Int),n044Q⟩

def n045NumPart0 : Poly := [(pm0, (600669 : Int)), (pm1, (-8255925 : Int)), (pm2, (38418828 : Int)), (pm3, (-63975720 : Int)), (pm4, (16992288 : Int)), (pm5, (-5056315 : Int))]
def n045Num : Poly := n045NumPart0

def n045NF : NF := ⟨n045Num,(2562890625 : Int)⟩
def n045QPart0 : Poly := [(pm0, (-29419421484375 : Int)), (pm1, (1594733062500000 : Int)), (pm2, (-1195245049218750 : Int)), (pm3, (428423048437500 : Int)), (pm4, (79975001953125 : Int))]
def n045Q : Poly := n045QPart0

def n045Row : Row := ⟨n045NF,.mul 18 18,(1 : Int),n045Q⟩

def n046NumPart0 : Poly := [(pm0, (-6989849856 : Int)), (pm1, (101702179584 : Int)), (pm2, (-524264460288 : Int)), (pm3, (1106408681472 : Int)), (pm4, (-824952349440 : Int)), (pm5, (277024806400 : Int))]
def n046Num : Poly := n046NumPart0

def n046NF : NF := ⟨n046Num,(263671875 : Int)⟩
def n046QPart0 : Poly := [(pm0, (-663489654300000000 : Int))]
def n046Q : Poly := n046QPart0

def n046Row : Row := ⟨n046NF,.mul 44 45,(1 : Int),n046Q⟩

def n047NumPart0 : Poly := [(pm0, (6989849856 : Int)), (pm1, (-101702179584 : Int)), (pm2, (524264460288 : Int)), (pm3, (-1106408681472 : Int)), (pm4, (824952349440 : Int)), (pm5, (-277024806400 : Int))]
def n047Num : Poly := n047NumPart0

def n047NF : NF := ⟨n047Num,(263671875 : Int)⟩
def n047QPart0 : Poly := []
def n047Q : Poly := n047QPart0

def n047Row : Row := ⟨n047NF,.mul 13 46,(1 : Int),n047Q⟩

def n048NumPart0 : Poly := [(pm0, (-473314479408 : Int)), (pm1, (6695452323792 : Int)), (pm2, (-32894546411904 : Int)), (pm3, (63014657627136 : Int)), (pm4, (-37115922793680 : Int)), (pm5, (16481707558000 : Int))]
def n048Num : Poly := n048NumPart0

def n048NF : NF := ⟨n048Num,(791015625 : Int)⟩
def n048QPart0 : Poly := []
def n048Q : Poly := n048QPart0

def n048Row : Row := ⟨n048NF,.add 42 47,(1 : Int),n048Q⟩

def n049NumPart0 : Poly := [(pm1, (9216 : Int))]
def n049Num : Poly := n049NumPart0

def n049NF : NF := ⟨n049Num,(1 : Int)⟩
def n049QPart0 : Poly := []
def n049Q : Poly := n049QPart0

def n049Row : Row := ⟨n049NF,.mul 0 16,(1 : Int),n049Q⟩

def n050NumPart0 : Poly := [(pm0, (-2813184 : Int)), (pm1, (-7029504 : Int)), (pm2, (674853888 : Int)), (pm3, (-4748255232 : Int)), (pm4, (9723168000 : Int)), (pm5, (-1065555200 : Int))]
def n050Num : Poly := n050NumPart0

def n050NF : NF := ⟨n050Num,(31640625 : Int)⟩
def n050QPart0 : Poly := [(pm0, (-23736240000000 : Int))]
def n050Q : Poly := n050QPart0

def n050Row : Row := ⟨n050NF,.mul 28 49,(1 : Int),n050Q⟩

def n051NumPart0 : Poly := [(pm0, (2813184 : Int)), (pm1, (7029504 : Int)), (pm2, (-674853888 : Int)), (pm3, (4748255232 : Int)), (pm4, (-9723168000 : Int)), (pm5, (1065555200 : Int))]
def n051Num : Poly := n051NumPart0

def n051NF : NF := ⟨n051Num,(31640625 : Int)⟩
def n051QPart0 : Poly := []
def n051Q : Poly := n051QPart0

def n051Row : Row := ⟨n051NF,.mul 13 50,(1 : Int),n051Q⟩

def n052NumPart0 : Poly := [(pm0, (-157748049936 : Int)), (pm1, (2231876020464 : Int)), (pm2, (-10970472586368 : Int)), (pm3, (21044454669312 : Int)), (pm4, (-12453000664560 : Int)), (pm5, (5502782146000 : Int))]
def n052Num : Poly := n052NumPart0

def n052NF : NF := ⟨n052Num,(263671875 : Int)⟩
def n052QPart0 : Poly := []
def n052Q : Poly := n052QPart0

def n052Row : Row := ⟨n052NF,.add 48 51,(1 : Int),n052Q⟩

def n053NumPart0 : Poly := [(pm0, (46656 : Int))]
def n053Num : Poly := n053NumPart0

def n053NF : NF := ⟨n053Num,(1 : Int)⟩
def n053QPart0 : Poly := []
def n053Q : Poly := n053QPart0

def n053Row : Row := ⟨n053NF,.lit (46656 : Int) (1 : Int),(1 : Int),n053Q⟩

def n054NumPart0 : Poly := [(pm0, (-82267632153 : Int)), (pm1, (1151282471607 : Int)), (pm2, (-5539714328904 : Int)), (pm3, (10070880027456 : Int)), (pm4, (-4759210412775 : Int)), (pm5, (2023149776725 : Int))]
def n054Num : Poly := n054NumPart0

def n054NF : NF := ⟨n054Num,(288325195312500 : Int)⟩
def n054QPart0 : Poly := [(pm0, (-2733394339603406250000 : Int)), (pm1, (12565013434083632812500 : Int)), (pm2, (-31268362620355664062500 : Int)), (pm3, (8177288837159179687500 : Int)), (pm4, (-2624153417885742187500 : Int))]
def n054Q : Poly := n054QPart0

def n054Row : Row := ⟨n054NF,.mul 1 45,(1 : Int),n054Q⟩

def n055NumPart0 : Poly := [(pm0, (-1316282114448 : Int)), (pm1, (18420519545712 : Int)), (pm2, (-88635429262464 : Int)), (pm3, (161134080439296 : Int)), (pm4, (-76147366604400 : Int)), (pm5, (32370396427600 : Int))]
def n055Num : Poly := n055NumPart0

def n055NF : NF := ⟨n055Num,(98876953125 : Int)⟩
def n055QPart0 : Poly := []
def n055Q : Poly := n055QPart0

def n055Row : Row := ⟨n055NF,.mul 53 54,(1 : Int),n055Q⟩

def n056NumPart0 : Poly := [(pm0, (-60471800840448 : Int)), (pm1, (855374027219712 : Int)), (pm2, (-4202562649150464 : Int)), (pm3, (8052804581431296 : Int)), (pm4, (-4746022615814400 : Int)), (pm5, (2095913701177600 : Int))]
def n056Num : Poly := n056NumPart0

def n056NF : NF := ⟨n056Num,(98876953125 : Int)⟩
def n056QPart0 : Poly := []
def n056Q : Poly := n056QPart0

def n056Row : Row := ⟨n056NF,.add 52 55,(1 : Int),n056Q⟩

def n057NumPart0 : Poly := [(pm0, (307542528 : Int)), (pm1, (-4227033600 : Int)), (pm2, (19670439936 : Int)), (pm3, (-32755568640 : Int)), (pm4, (8700051456 : Int)), (pm5, (-2588833280 : Int))]
def n057Num : Poly := n057NumPart0

def n057NF : NF := ⟨n057Num,(94921875 : Int)⟩
def n057QPart0 : Poly := []
def n057Q : Poly := n057QPart0

def n057Row : Row := ⟨n057NF,.mul 26 45,(1 : Int),n057Q⟩

def n058NumPart0 : Poly := [(pm0, (-180454332121344 : Int)), (pm1, (2552912601659136 : Int)), (pm2, (-12546217822651392 : Int)), (pm3, (24056052592293888 : Int)), (pm4, (-14210880186643200 : Int)), (pm5, (6279650999532800 : Int))]
def n058Num : Poly := n058NumPart0

def n058NF : NF := ⟨n058Num,(296630859375 : Int)⟩
def n058QPart0 : Poly := []
def n058Q : Poly := n058QPart0

def n058Row : Row := ⟨n058NF,.add 56 57,(1 : Int),n058Q⟩

def n059NumPart0 : Poly := [(pm0, (-9282816 : Int)), (pm1, (172917504 : Int)), (pm2, (-1018917888 : Int)), (pm3, (1978079232 : Int)), (pm4, (-226656000 : Int)), (pm5, (-2604800 : Int))]
def n059Num : Poly := n059NumPart0

def n059NF : NF := ⟨n059Num,(56953125 : Int)⟩
def n059QPart0 : Poly := []
def n059Q : Poly := n059QPart0

def n059Row : Row := ⟨n059NF,.mul 2 28,(1 : Int),n059Q⟩

def n060NumPart0 : Poly := [(pm0, (-541508040364032 : Int)), (pm1, (7661439640977408 : Int)), (pm2, (-37654574059954176 : Int)), (pm3, (72199065264881664 : Int)), (pm4, (-42636182059929600 : Int)), (pm5, (18838912298598400 : Int))]
def n060Num : Poly := n060NumPart0

def n060NF : NF := ⟨n060Num,(889892578125 : Int)⟩
def n060QPart0 : Poly := []
def n060Q : Poly := n060QPart0

def n060Row : Row := ⟨n060NF,.add 58 59,(1 : Int),n060Q⟩

def n061NumPart0 : Poly := [(pm0, (-702 : Int)), (pm1, (9963 : Int)), (pm2, (-49236 : Int)), (pm3, (95529 : Int)), (pm4, (-58350 : Int)), (pm5, (24925 : Int))]
def n061Num : Poly := n061NumPart0

def n061NF : NF := ⟨n061Num,(625 : Int)⟩
def n061QPart0 : Poly := [(pm0, (-3250 : Int))]
def n061Q : Poly := n061QPart0

def n061Row : Row := ⟨n061NF,.mul 0 5,(1 : Int),n061Q⟩

def n062NumPart0 : Poly := [(pm0, (-718848 : Int)), (pm1, (10202112 : Int)), (pm2, (-50417664 : Int)), (pm3, (97821696 : Int)), (pm4, (-59750400 : Int)), (pm5, (25523200 : Int))]
def n062Num : Poly := n062NumPart0

def n062NF : NF := ⟨n062Num,(625 : Int)⟩
def n062QPart0 : Poly := []
def n062Q : Poly := n062QPart0

def n062Row : Row := ⟨n062NF,.mul 2 61,(1 : Int),n062Q⟩

def n063NumPart0 : Poly := [(pm0, (13824 : Int)), (pm1, (-193536 : Int)), (pm2, (932352 : Int)), (pm3, (-1701888 : Int)), (pm4, (821760 : Int)), (pm5, (-332800 : Int))]
def n063Num : Poly := n063NumPart0

def n063NF : NF := ⟨n063Num,(125 : Int)⟩
def n063QPart0 : Poly := []
def n063Q : Poly := n063QPart0

def n063Row : Row := ⟨n063NF,.mul 5 8,(1 : Int),n063Q⟩

def n064NumPart0 : Poly := [(pm0, (-13824 : Int)), (pm1, (193536 : Int)), (pm2, (-932352 : Int)), (pm3, (1701888 : Int)), (pm4, (-821760 : Int)), (pm5, (332800 : Int))]
def n064Num : Poly := n064NumPart0

def n064NF : NF := ⟨n064Num,(125 : Int)⟩
def n064QPart0 : Poly := []
def n064Q : Poly := n064QPart0

def n064Row : Row := ⟨n064NF,.mul 13 63,(1 : Int),n064Q⟩

def n065NumPart0 : Poly := [(pm0, (-787968 : Int)), (pm1, (11169792 : Int)), (pm2, (-55079424 : Int)), (pm3, (106331136 : Int)), (pm4, (-63859200 : Int)), (pm5, (27187200 : Int))]
def n065Num : Poly := n065NumPart0

def n065NF : NF := ⟨n065Num,(625 : Int)⟩
def n065QPart0 : Poly := []
def n065Q : Poly := n065QPart0

def n065Row : Row := ⟨n065NF,.add 62 64,(1 : Int),n065Q⟩

def n066NumPart0 : Poly := [(pm0, (3072 : Int))]
def n066Num : Poly := n066NumPart0

def n066NF : NF := ⟨n066Num,(1 : Int)⟩
def n066QPart0 : Poly := []
def n066Q : Poly := n066QPart0

def n066Row : Row := ⟨n066NF,.lit (3072 : Int) (1 : Int),(1 : Int),n066Q⟩

def n067NumPart0 : Poly := [(pm5, (3072 : Int))]
def n067Num : Poly := n067NumPart0

def n067NF : NF := ⟨n067Num,(1 : Int)⟩
def n067QPart0 : Poly := []
def n067Q : Poly := n067QPart0

def n067Row : Row := ⟨n067NF,.mul 10 66,(1 : Int),n067Q⟩

def n068NumPart0 : Poly := [(pm0, (7803648 : Int)), (pm1, (-109216512 : Int)), (pm2, (529112064 : Int)), (pm3, (-994845696 : Int)), (pm4, (586886400 : Int)), (pm5, (-327737600 : Int))]
def n068Num : Poly := n068NumPart0

def n068NF : NF := ⟨n068Num,(46875 : Int)⟩
def n068QPart0 : Poly := [(pm0, (52024320 : Int)), (pm1, (230400 : Int)), (pm2, (21888000 : Int)), (pm3, (63360000 : Int)), (pm4, (259200000 : Int))]
def n068Q : Poly := n068QPart0

def n068Row : Row := ⟨n068NF,.mul 1 67,(1 : Int),n068Q⟩

def n069NumPart0 : Poly := [(pm0, (-51293952 : Int)), (pm1, (728517888 : Int)), (pm2, (-3601844736 : Int)), (pm3, (6979989504 : Int)), (pm4, (-4202553600 : Int)), (pm5, (1711302400 : Int))]
def n069Num : Poly := n069NumPart0

def n069NF : NF := ⟨n069Num,(46875 : Int)⟩
def n069QPart0 : Poly := []
def n069Q : Poly := n069QPart0

def n069Row : Row := ⟨n069NF,.add 65 68,(1 : Int),n069Q⟩

def n070NumPart0 : Poly := [(pm5, (64 : Int))]
def n070Num : Poly := n070NumPart0

def n070NF : NF := ⟨n070Num,(1 : Int)⟩
def n070QPart0 : Poly := []
def n070Q : Poly := n070QPart0

def n070Row : Row := ⟨n070NF,.mul 10 22,(1 : Int),n070Q⟩

def n071NumPart0 : Poly := [(pm0, (-51293952 : Int)), (pm1, (728517888 : Int)), (pm2, (-3601844736 : Int)), (pm3, (6979989504 : Int)), (pm4, (-4202553600 : Int)), (pm5, (1714302400 : Int))]
def n071Num : Poly := n071NumPart0

def n071NF : NF := ⟨n071Num,(46875 : Int)⟩
def n071QPart0 : Poly := []
def n071Q : Poly := n071QPart0

def n071Row : Row := ⟨n071NF,.add 69 70,(1 : Int),n071Q⟩

def n072NumPart0 : Poly := [(pm0, (96768 : Int))]
def n072Num : Poly := n072NumPart0

def n072NF : NF := ⟨n072Num,(1 : Int)⟩
def n072QPart0 : Poly := []
def n072Q : Poly := n072QPart0

def n072Row : Row := ⟨n072NF,.lit (96768 : Int) (1 : Int),(1 : Int),n072Q⟩

def n073NumPart0 : Poly := [(pm4, (96768 : Int))]
def n073Num : Poly := n073NumPart0

def n073NF : NF := ⟨n073Num,(1 : Int)⟩
def n073QPart0 : Poly := []
def n073Q : Poly := n073QPart0

def n073Row : Row := ⟨n073NF,.mul 9 72,(1 : Int),n073Q⟩

def n074NumPart0 : Poly := [(pm0, (2576496384 : Int)), (pm1, (-36770340096 : Int)), (pm2, (183599334912 : Int)), (pm3, (-364412525568 : Int)), (pm4, (236945721600 : Int)), (pm5, (-94409772800 : Int))]
def n074Num : Poly := n074NumPart0

def n074NF : NF := ⟨n074Num,(1171875 : Int)⟩
def n074QPart0 : Poly := [(pm0, (9661861440000 : Int)), (pm1, (-2622715200000 : Int)), (pm2, (140616000000 : Int)), (pm3, (1791720000000 : Int))]
def n074Q : Poly := n074QPart0

def n074Row : Row := ⟨n074NF,.mul 18 73,(1 : Int),n074Q⟩

def n075NumPart0 : Poly := [(pm0, (-2576496384 : Int)), (pm1, (36770340096 : Int)), (pm2, (-183599334912 : Int)), (pm3, (364412525568 : Int)), (pm4, (-236945721600 : Int)), (pm5, (94409772800 : Int))]
def n075Num : Poly := n075NumPart0

def n075NF : NF := ⟨n075Num,(1171875 : Int)⟩
def n075QPart0 : Poly := []
def n075Q : Poly := n075QPart0

def n075Row : Row := ⟨n075NF,.mul 13 74,(1 : Int),n075Q⟩

def n076NumPart0 : Poly := [(pm0, (-1286281728 : Int)), (pm1, (18327762432 : Int)), (pm2, (-91215151104 : Int)), (pm3, (179637421056 : Int)), (pm4, (-114003187200 : Int)), (pm5, (45755777600 : Int))]
def n076Num : Poly := n076NumPart0

def n076NF : NF := ⟨n076Num,(390625 : Int)⟩
def n076QPart0 : Poly := []
def n076Q : Poly := n076QPart0

def n076Row : Row := ⟨n076NF,.add 71 75,(1 : Int),n076Q⟩

def n077NumPart0 : Poly := [(pm0, (2816 : Int))]
def n077Num : Poly := n077NumPart0

def n077NF : NF := ⟨n077Num,(1 : Int)⟩
def n077QPart0 : Poly := []
def n077Q : Poly := n077QPart0

def n077Row : Row := ⟨n077NF,.lit (2816 : Int) (1 : Int),(1 : Int),n077Q⟩

def n078NumPart0 : Poly := [(pm4, (2816 : Int))]
def n078Num : Poly := n078NumPart0

def n078NF : NF := ⟨n078Num,(1 : Int)⟩
def n078QPart0 : Poly := []
def n078Q : Poly := n078QPart0

def n078Row : Row := ⟨n078NF,.mul 9 77,(1 : Int),n078Q⟩

def n079NumPart0 : Poly := [(pm0, (19008 : Int)), (pm1, (1539648 : Int)), (pm2, (-18771456 : Int)), (pm3, (67651584 : Int)), (pm4, (-76929600 : Int)), (pm5, (19870400 : Int))]
def n079Num : Poly := n079NumPart0

def n079NF : NF := ⟨n079Num,(28125 : Int)⟩
def n079QPart0 : Poly := [(pm0, (126720 : Int)), (pm1, (12038400 : Int)), (pm2, (34848000 : Int)), (pm3, (142560000 : Int))]
def n079Q : Poly := n079QPart0

def n079Row : Row := ⟨n079NF,.mul 1 78,(1 : Int),n079Q⟩

def n080NumPart0 : Poly := [(pm0, (-19008 : Int)), (pm1, (-1539648 : Int)), (pm2, (18771456 : Int)), (pm3, (-67651584 : Int)), (pm4, (76929600 : Int)), (pm5, (-19870400 : Int))]
def n080Num : Poly := n080NumPart0

def n080NF : NF := ⟨n080Num,(28125 : Int)⟩
def n080QPart0 : Poly := []
def n080Q : Poly := n080QPart0

def n080Row : Row := ⟨n080NF,.mul 13 79,(1 : Int),n080Q⟩

def n081NumPart0 : Poly := [(pm0, (-11578911552 : Int)), (pm1, (164757405888 : Int)), (pm2, (-818589927936 : Int)), (pm3, (1608280341504 : Int)), (pm4, (-1016412484800 : Int)), (pm5, (409318198400 : Int))]
def n081Num : Poly := n081NumPart0

def n081NF : NF := ⟨n081Num,(3515625 : Int)⟩
def n081QPart0 : Poly := []
def n081Q : Poly := n081QPart0

def n081Row : Row := ⟨n081NF,.add 76 80,(1 : Int),n081Q⟩

def n082NumPart0 : Poly := [(pm0, (26496 : Int))]
def n082Num : Poly := n082NumPart0

def n082NF : NF := ⟨n082Num,(1 : Int)⟩
def n082QPart0 : Poly := []
def n082Q : Poly := n082QPart0

def n082Row : Row := ⟨n082NF,.lit (26496 : Int) (1 : Int),(1 : Int),n082Q⟩

def n083NumPart0 : Poly := [(pm3, (26496 : Int))]
def n083Num : Poly := n083NumPart0

def n083NF : NF := ⟨n083Num,(1 : Int)⟩
def n083QPart0 : Poly := []
def n083Q : Poly := n083QPart0

def n083Row : Row := ⟨n083NF,.mul 4 82,(1 : Int),n083Q⟩

def n084NumPart0 : Poly := [(pm0, (-114899904 : Int)), (pm1, (1614758976 : Int)), (pm2, (-7757110272 : Int)), (pm3, (13765060608 : Int)), (pm4, (-5320065600 : Int)), (pm5, (1959636800 : Int))]
def n084Num : Poly := n084NumPart0

def n084NF : NF := ⟨n084Num,(703125 : Int)⟩
def n084QPart0 : Poly := [(pm0, (-430874640000 : Int)), (pm1, (23101200000 : Int)), (pm2, (294354000000 : Int))]
def n084Q : Poly := n084QPart0

def n084Row : Row := ⟨n084NF,.mul 18 83,(1 : Int),n084Q⟩

def n085NumPart0 : Poly := [(pm0, (-4051137024 : Int)), (pm1, (57610400256 : Int)), (pm2, (-285791826432 : Int)), (pm3, (559035214848 : Int)), (pm4, (-347670937600 : Int)), (pm5, (139705460800 : Int))]
def n085Num : Poly := n085NumPart0

def n085NF : NF := ⟨n085Num,(1171875 : Int)⟩
def n085QPart0 : Poly := []
def n085Q : Poly := n085QPart0

def n085Row : Row := ⟨n085NF,.add 81 84,(1 : Int),n085Q⟩

def n086NumPart0 : Poly := [(pm3, (512 : Int))]
def n086Num : Poly := n086NumPart0

def n086NF : NF := ⟨n086Num,(1 : Int)⟩
def n086QPart0 : Poly := []
def n086Q : Poly := n086QPart0

def n086Row : Row := ⟨n086NF,.mul 4 8,(1 : Int),n086Q⟩

def n087NumPart0 : Poly := [(pm0, (65664 : Int)), (pm1, (-729216 : Int)), (pm2, (2545152 : Int)), (pm3, (-2838528 : Int)), (pm4, (739200 : Int)), (pm5, (3200 : Int))]
def n087Num : Poly := n087NumPart0

def n087NF : NF := ⟨n087Num,(5625 : Int)⟩
def n087QPart0 : Poly := [(pm0, (437760 : Int)), (pm1, (1267200 : Int)), (pm2, (5184000 : Int))]
def n087Q : Poly := n087QPart0

def n087Row : Row := ⟨n087NF,.mul 1 86,(1 : Int),n087Q⟩

def n088NumPart0 : Poly := [(pm0, (-12112371072 : Int)), (pm1, (172375440768 : Int)), (pm2, (-855784759296 : Int)), (pm3, (1675331564544 : Int)), (pm4, (-1042550812800 : Int)), (pm5, (419118382400 : Int))]
def n088Num : Poly := n088NumPart0

def n088NF : NF := ⟨n088Num,(3515625 : Int)⟩
def n088QPart0 : Poly := []
def n088Q : Poly := n088QPart0

def n088Row : Row := ⟨n088NF,.add 85 87,(1 : Int),n088Q⟩

def n089NumPart0 : Poly := [(pm0, (518400 : Int))]
def n089Num : Poly := n089NumPart0

def n089NF : NF := ⟨n089Num,(1 : Int)⟩
def n089QPart0 : Poly := []
def n089Q : Poly := n089QPart0

def n089Row : Row := ⟨n089NF,.lit (518400 : Int) (1 : Int),(1 : Int),n089Q⟩

def n090NumPart0 : Poly := [(pm2, (518400 : Int))]
def n090Num : Poly := n090NumPart0

def n090NF : NF := ⟨n090Num,(1 : Int)⟩
def n090QPart0 : Poly := []
def n090Q : Poly := n090QPart0

def n090Row : Row := ⟨n090NF,.mul 3 89,(1 : Int),n090Q⟩

def n091NumPart0 : Poly := [(pm0, (-287699904 : Int)), (pm1, (4024282176 : Int)), (pm2, (-19412547072 : Int)), (pm3, (36262622208 : Int)), (pm4, (-23037480000 : Int)), (pm5, (19080068800 : Int))]
def n091Num : Poly := n091NumPart0

def n091NF : NF := ⟨n091Num,(703125 : Int)⟩
def n091QPart0 : Poly := [(pm0, (-2427467940000000 : Int)), (pm1, (-29670300000000 : Int))]
def n091Q : Poly := n091QPart0

def n091Row : Row := ⟨n091NF,.mul 28 90,(1 : Int),n091Q⟩

def n092NumPart0 : Poly := [(pm0, (-13550870592 : Int)), (pm1, (192496851648 : Int)), (pm2, (-952847494656 : Int)), (pm3, (1856644675584 : Int)), (pm4, (-1157738212800 : Int)), (pm5, (514518726400 : Int))]
def n092Num : Poly := n092NumPart0

def n092NF : NF := ⟨n092Num,(3515625 : Int)⟩
def n092QPart0 : Poly := []
def n092Q : Poly := n092QPart0

def n092Row : Row := ⟨n092NF,.add 88 91,(1 : Int),n092Q⟩

def n093NumPart0 : Poly := [(pm0, (12288 : Int))]
def n093Num : Poly := n093NumPart0

def n093NF : NF := ⟨n093Num,(1 : Int)⟩
def n093QPart0 : Poly := []
def n093Q : Poly := n093QPart0

def n093Row : Row := ⟨n093NF,.lit (12288 : Int) (1 : Int),(1 : Int),n093Q⟩

def n094NumPart0 : Poly := [(pm2, (12288 : Int))]
def n094Num : Poly := n094NumPart0

def n094NF : NF := ⟨n094Num,(1 : Int)⟩
def n094QPart0 : Poly := []
def n094Q : Poly := n094QPart0

def n094Row : Row := ⟨n094NF,.mul 3 93,(1 : Int),n094Q⟩

def n095NumPart0 : Poly := [(pm0, (1714176 : Int)), (pm1, (-2156544 : Int)), (pm2, (-105848832 : Int)), (pm3, (420200448 : Int)), (pm4, (-224409600 : Int)), (pm5, (-148019200 : Int))]
def n095Num : Poly := n095NumPart0

def n095NF : NF := ⟨n095Num,(421875 : Int)⟩
def n095QPart0 : Poly := [(pm0, (6428160000 : Int)), (pm1, (81907200000 : Int))]
def n095Q : Poly := n095QPart0

def n095Row : Row := ⟨n095NF,.mul 18 94,(1 : Int),n095Q⟩

def n096NumPart0 : Poly := [(pm0, (-40609757376 : Int)), (pm1, (577436641344 : Int)), (pm2, (-2861188704768 : Int)), (pm3, (5580439037952 : Int)), (pm4, (-3478824878400 : Int)), (pm5, (1539855699200 : Int))]
def n096Num : Poly := n096NumPart0

def n096NF : NF := ⟨n096Num,(10546875 : Int)⟩
def n096QPart0 : Poly := []
def n096Q : Poly := n096QPart0

def n096Row : Row := ⟨n096NF,.add 92 95,(1 : Int),n096Q⟩

def n097NumPart0 : Poly := [(pm0, (699840 : Int))]
def n097Num : Poly := n097NumPart0

def n097NF : NF := ⟨n097Num,(1 : Int)⟩
def n097QPart0 : Poly := []
def n097Q : Poly := n097QPart0

def n097Row : Row := ⟨n097NF,.lit (699840 : Int) (1 : Int),(1 : Int),n097Q⟩

def n098NumPart0 : Poly := [(pm1, (699840 : Int))]
def n098Num : Poly := n098NumPart0

def n098NF : NF := ⟨n098Num,(1 : Int)⟩
def n098QPart0 : Poly := []
def n098Q : Poly := n098QPart0

def n098Row : Row := ⟨n098NF,.mul 0 97,(1 : Int),n098Q⟩

def n099NumPart0 : Poly := [(pm0, (-1747462464 : Int)), (pm1, (25425544896 : Int)), (pm2, (-131066115072 : Int)), (pm3, (276602170368 : Int)), (pm4, (-206238087360 : Int)), (pm5, (69256201600 : Int))]
def n099Num : Poly := n099NumPart0

def n099NF : NF := ⟨n099Num,(5859375 : Int)⟩
def n099QPart0 : Poly := [(pm0, (-165872413575000000 : Int))]
def n099Q : Poly := n099QPart0

def n099Row : Row := ⟨n099NF,.mul 45 98,(1 : Int),n099Q⟩

def n100NumPart0 : Poly := [(pm0, (1747462464 : Int)), (pm1, (-25425544896 : Int)), (pm2, (131066115072 : Int)), (pm3, (-276602170368 : Int)), (pm4, (206238087360 : Int)), (pm5, (-69256201600 : Int))]
def n100Num : Poly := n100NumPart0

def n100NF : NF := ⟨n100Num,(5859375 : Int)⟩
def n100QPart0 : Poly := []
def n100Q : Poly := n100QPart0

def n100Row : Row := ⟨n100NF,.mul 13 99,(1 : Int),n100Q⟩

def n101NumPart0 : Poly := [(pm0, (-187321624704 : Int)), (pm1, (2658353302656 : Int)), (pm2, (-13126348488192 : Int)), (pm3, (25412775656448 : Int)), (pm4, (-15537981605760 : Int)), (pm5, (7075972681600 : Int))]
def n101Num : Poly := n101NumPart0

def n101NF : NF := ⟨n101Num,(52734375 : Int)⟩
def n101QPart0 : Poly := []
def n101Q : Poly := n101QPart0

def n101Row : Row := ⟨n101NF,.add 96 100,(1 : Int),n101Q⟩

def n102NumPart0 : Poly := [(pm0, (290304 : Int))]
def n102Num : Poly := n102NumPart0

def n102NF : NF := ⟨n102Num,(1 : Int)⟩
def n102QPart0 : Poly := []
def n102Q : Poly := n102QPart0

def n102Row : Row := ⟨n102NF,.lit (290304 : Int) (1 : Int),(1 : Int),n102Q⟩

def n103NumPart0 : Poly := [(pm1, (290304 : Int))]
def n103Num : Poly := n103NumPart0

def n103NF : NF := ⟨n103Num,(1 : Int)⟩
def n103QPart0 : Poly := []
def n103Q : Poly := n103QPart0

def n103Row : Row := ⟨n103NF,.mul 0 102,(1 : Int),n103Q⟩

def n104NumPart0 : Poly := [(pm0, (-9846144 : Int)), (pm1, (-24603264 : Int)), (pm2, (2361988608 : Int)), (pm3, (-16618893312 : Int)), (pm4, (34031088000 : Int)), (pm5, (-3729443200 : Int))]
def n104Num : Poly := n104NumPart0

def n104NF : NF := ⟨n104Num,(3515625 : Int)⟩
def n104QPart0 : Poly := [(pm0, (-83076840000000 : Int))]
def n104Q : Poly := n104QPart0

def n104Row : Row := ⟨n104NF,.mul 28 103,(1 : Int),n104Q⟩

def n105NumPart0 : Poly := [(pm0, (9846144 : Int)), (pm1, (24603264 : Int)), (pm2, (-2361988608 : Int)), (pm3, (16618893312 : Int)), (pm4, (-34031088000 : Int)), (pm5, (3729443200 : Int))]
def n105Num : Poly := n105NumPart0

def n105NF : NF := ⟨n105Num,(3515625 : Int)⟩
def n105QPart0 : Poly := []
def n105Q : Poly := n105QPart0

def n105Row : Row := ⟨n105NF,.mul 13 104,(1 : Int),n105Q⟩

def n106NumPart0 : Poly := [(pm0, (-187173932544 : Int)), (pm1, (2658722351616 : Int)), (pm2, (-13161778317312 : Int)), (pm3, (25662059056128 : Int)), (pm4, (-16048447925760 : Int)), (pm5, (7131914329600 : Int))]
def n106Num : Poly := n106NumPart0

def n106NF : NF := ⟨n106Num,(52734375 : Int)⟩
def n106QPart0 : Poly := []
def n106Q : Poly := n106QPart0

def n106Row : Row := ⟨n106NF,.add 101 105,(1 : Int),n106Q⟩

def n107NumPart0 : Poly := [(pm1, (3072 : Int))]
def n107Num : Poly := n107NumPart0

def n107NF : NF := ⟨n107Num,(1 : Int)⟩
def n107QPart0 : Poly := []
def n107Q : Poly := n107QPart0

def n107Row : Row := ⟨n107NF,.mul 0 66,(1 : Int),n107Q⟩

def n108NumPart0 : Poly := [(pm0, (1092096 : Int)), (pm1, (-11073024 : Int)), (pm2, (31561728 : Int)), (pm3, (-16315392 : Int)), (pm4, (-5337600 : Int)), (pm5, (396800 : Int))]
def n108Num : Poly := n108NumPart0

def n108NF : NF := ⟨n108Num,(84375 : Int)⟩
def n108QPart0 : Poly := [(pm0, (4095360000 : Int))]
def n108Q : Poly := n108QPart0

def n108Row : Row := ⟨n108NF,.mul 18 107,(1 : Int),n108Q⟩

def n109NumPart0 : Poly := [(pm0, (-1092096 : Int)), (pm1, (11073024 : Int)), (pm2, (-31561728 : Int)), (pm3, (16315392 : Int)), (pm4, (5337600 : Int)), (pm5, (-396800 : Int))]
def n109Num : Poly := n109NumPart0

def n109NF : NF := ⟨n109Num,(84375 : Int)⟩
def n109QPart0 : Poly := []
def n109Q : Poly := n109QPart0

def n109Row : Row := ⟨n109NF,.mul 13 108,(1 : Int),n109Q⟩

def n110NumPart0 : Poly := [(pm0, (-187856492544 : Int)), (pm1, (2665642991616 : Int)), (pm2, (-13181504397312 : Int)), (pm3, (25672256176128 : Int)), (pm4, (-16045111925760 : Int)), (pm5, (7131666329600 : Int))]
def n110Num : Poly := n110NumPart0

def n110NF : NF := ⟨n110Num,(52734375 : Int)⟩
def n110QPart0 : Poly := []
def n110Q : Poly := n110QPart0

def n110Row : Row := ⟨n110NF,.add 106 109,(1 : Int),n110Q⟩

def n111NumPart0 : Poly := [(pm0, (248832 : Int))]
def n111Num : Poly := n111NumPart0

def n111NF : NF := ⟨n111Num,(1 : Int)⟩
def n111QPart0 : Poly := []
def n111Q : Poly := n111QPart0

def n111Row : Row := ⟨n111NF,.lit (248832 : Int) (1 : Int),(1 : Int),n111Q⟩

def n112NumPart0 : Poly := [(pm0, (615085056 : Int)), (pm1, (-8454067200 : Int)), (pm2, (39340879872 : Int)), (pm3, (-65511137280 : Int)), (pm4, (17400102912 : Int)), (pm5, (-5177666560 : Int))]
def n112Num : Poly := n112NumPart0

def n112NF : NF := ⟨n112Num,(10546875 : Int)⟩
def n112QPart0 : Poly := []
def n112Q : Poly := n112QPart0

def n112Row : Row := ⟨n112NF,.mul 45 111,(1 : Int),n112Q⟩

def n113NumPart0 : Poly := [(pm0, (-61593689088 : Int)), (pm1, (874457551872 : Int)), (pm2, (-4328266665984 : Int)), (pm3, (8448233496576 : Int)), (pm4, (-5319370470400 : Int)), (pm5, (2368592665600 : Int))]
def n113Num : Poly := n113NumPart0

def n113NF : NF := ⟨n113Num,(17578125 : Int)⟩
def n113QPart0 : Poly := []
def n113Q : Poly := n113QPart0

def n113Row : Row := ⟨n113NF,.add 110 112,(1 : Int),n113Q⟩

def n114NumPart0 : Poly := [(pm0, (36864 : Int))]
def n114Num : Poly := n114NumPart0

def n114NF : NF := ⟨n114Num,(1 : Int)⟩
def n114QPart0 : Poly := []
def n114Q : Poly := n114QPart0

def n114Row : Row := ⟨n114NF,.lit (36864 : Int) (1 : Int),(1 : Int),n114Q⟩

def n115NumPart0 : Poly := [(pm0, (-37131264 : Int)), (pm1, (691670016 : Int)), (pm2, (-4075671552 : Int)), (pm3, (7912316928 : Int)), (pm4, (-906624000 : Int)), (pm5, (-10419200 : Int))]
def n115Num : Poly := n115NumPart0

def n115NF : NF := ⟨n115Num,(6328125 : Int)⟩
def n115QPart0 : Poly := []
def n115Q : Poly := n115QPart0

def n115Row : Row := ⟨n115NF,.mul 28 114,(1 : Int),n115Q⟩

def n116NumPart0 : Poly := [(pm0, (-555271483392 : Int)), (pm1, (7887409717248 : Int)), (pm2, (-39056291782656 : Int)), (pm3, (76231909392384 : Int)), (pm4, (-47896999833600 : Int)), (pm5, (21317073510400 : Int))]
def n116Num : Poly := n116NumPart0

def n116NF : NF := ⟨n116Num,(158203125 : Int)⟩
def n116QPart0 : Poly := []
def n116Q : Poly := n116QPart0

def n116Row : Row := ⟨n116NF,.add 113 115,(1 : Int),n116Q⟩

def n117NumPart0 : Poly := [(pm0, (21504 : Int))]
def n117Num : Poly := n117NumPart0

def n117NF : NF := ⟨n117Num,(1 : Int)⟩
def n117QPart0 : Poly := []
def n117Q : Poly := n117QPart0

def n117Row : Row := ⟨n117NF,.lit (21504 : Int) (1 : Int),(1 : Int),n117Q⟩

def n118NumPart0 : Poly := [(pm0, (580608 : Int)), (pm1, (-8128512 : Int)), (pm2, (39158784 : Int)), (pm3, (-71479296 : Int)), (pm4, (34513920 : Int)), (pm5, (-13977600 : Int))]
def n118Num : Poly := n118NumPart0

def n118NF : NF := ⟨n118Num,(125 : Int)⟩
def n118QPart0 : Poly := []
def n118Q : Poly := n118QPart0

def n118Row : Row := ⟨n118NF,.mul 5 117,(1 : Int),n118Q⟩

def n119NumPart0 : Poly := [(pm0, (2322432 : Int))]
def n119Num : Poly := n119NumPart0

def n119NF : NF := ⟨n119Num,(1 : Int)⟩
def n119QPart0 : Poly := []
def n119Q : Poly := n119QPart0

def n119Row : Row := ⟨n119NF,.lit (2322432 : Int) (1 : Int),(1 : Int),n119Q⟩

def n120NumPart0 : Poly := [(pm5, (2322432 : Int))]
def n120Num : Poly := n120NumPart0

def n120NF : NF := ⟨n120Num,(1 : Int)⟩
def n120QPart0 : Poly := []
def n120Q : Poly := n120QPart0

def n120Row : Row := ⟨n120NF,.mul 10 119,(1 : Int),n120Q⟩

def n121NumPart0 : Poly := [(pm0, (1966519296 : Int)), (pm1, (-27522561024 : Int)), (pm2, (133336240128 : Int)), (pm3, (-250701115392 : Int)), (pm4, (147895372800 : Int)), (pm5, (-82589875200 : Int))]
def n121Num : Poly := n121NumPart0

def n121NF : NF := ⟨n121Num,(15625 : Int)⟩
def n121QPart0 : Poly := [(pm0, (13110128640 : Int)), (pm1, (58060800 : Int)), (pm2, (5515776000 : Int)), (pm3, (15966720000 : Int)), (pm4, (65318400000 : Int))]
def n121Q : Poly := n121QPart0

def n121Row : Row := ⟨n121NF,.mul 1 120,(1 : Int),n121Q⟩

def n122NumPart0 : Poly := [(pm0, (2039095296 : Int)), (pm1, (-28538625024 : Int)), (pm2, (138231088128 : Int)), (pm3, (-259636027392 : Int)), (pm4, (152209612800 : Int)), (pm5, (-84337075200 : Int))]
def n122Num : Poly := n122NumPart0

def n122NF : NF := ⟨n122Num,(15625 : Int)⟩
def n122QPart0 : Poly := []
def n122Q : Poly := n122QPart0

def n122Row : Row := ⟨n122NF,.add 118 121,(1 : Int),n122Q⟩

def n123NumPart0 : Poly := [(pm0, (11776 : Int))]
def n123Num : Poly := n123NumPart0

def n123NF : NF := ⟨n123Num,(1 : Int)⟩
def n123QPart0 : Poly := []
def n123Q : Poly := n123QPart0

def n123Row : Row := ⟨n123NF,.lit (11776 : Int) (1 : Int),(1 : Int),n123Q⟩

def n124NumPart0 : Poly := [(pm5, (11776 : Int))]
def n124Num : Poly := n124NumPart0

def n124NF : NF := ⟨n124Num,(1 : Int)⟩
def n124QPart0 : Poly := []
def n124Q : Poly := n124QPart0

def n124Row : Row := ⟨n124NF,.mul 10 123,(1 : Int),n124Q⟩

def n125NumPart0 : Poly := [(pm5, (-11776 : Int))]
def n125Num : Poly := n125NumPart0

def n125NF : NF := ⟨n125Num,(1 : Int)⟩
def n125QPart0 : Poly := []
def n125Q : Poly := n125QPart0

def n125Row : Row := ⟨n125NF,.mul 13 124,(1 : Int),n125Q⟩

def n126NumPart0 : Poly := [(pm0, (2039095296 : Int)), (pm1, (-28538625024 : Int)), (pm2, (138231088128 : Int)), (pm3, (-259636027392 : Int)), (pm4, (152209612800 : Int)), (pm5, (-84521075200 : Int))]
def n126Num : Poly := n126NumPart0

def n126NF : NF := ⟨n126Num,(15625 : Int)⟩
def n126QPart0 : Poly := []
def n126Q : Poly := n126QPart0

def n126Row : Row := ⟨n126NF,.add 122 125,(1 : Int),n126Q⟩

def n127NumPart0 : Poly := [(pm0, (1382400 : Int))]
def n127Num : Poly := n127NumPart0

def n127NF : NF := ⟨n127Num,(1 : Int)⟩
def n127QPart0 : Poly := []
def n127Q : Poly := n127QPart0

def n127Row : Row := ⟨n127NF,.lit (1382400 : Int) (1 : Int),(1 : Int),n127Q⟩

def n128NumPart0 : Poly := [(pm4, (1382400 : Int))]
def n128Num : Poly := n128NumPart0

def n128NF : NF := ⟨n128Num,(1 : Int)⟩
def n128QPart0 : Poly := []
def n128Q : Poly := n128QPart0

def n128Row : Row := ⟨n128NF,.mul 9 127,(1 : Int),n128Q⟩

def n129NumPart0 : Poly := [(pm0, (41472 : Int)), (pm1, (3359232 : Int)), (pm2, (-40955904 : Int)), (pm3, (147603456 : Int)), (pm4, (-167846400 : Int)), (pm5, (43353600 : Int))]
def n129Num : Poly := n129NumPart0

def n129NF : NF := ⟨n129Num,(125 : Int)⟩
def n129QPart0 : Poly := [(pm0, (276480 : Int)), (pm1, (26265600 : Int)), (pm2, (76032000 : Int)), (pm3, (311040000 : Int))]
def n129Q : Poly := n129QPart0

def n129Row : Row := ⟨n129NF,.mul 1 128,(1 : Int),n129Q⟩

def n130NumPart0 : Poly := [(pm0, (-41472 : Int)), (pm1, (-3359232 : Int)), (pm2, (40955904 : Int)), (pm3, (-147603456 : Int)), (pm4, (167846400 : Int)), (pm5, (-43353600 : Int))]
def n130Num : Poly := n130NumPart0

def n130NF : NF := ⟨n130Num,(125 : Int)⟩
def n130QPart0 : Poly := []
def n130Q : Poly := n130QPart0

def n130Row : Row := ⟨n130NF,.mul 13 129,(1 : Int),n130Q⟩

def n131NumPart0 : Poly := [(pm0, (2033911296 : Int)), (pm1, (-28958529024 : Int)), (pm2, (143350576128 : Int)), (pm3, (-278086459392 : Int)), (pm4, (173190412800 : Int)), (pm5, (-89940275200 : Int))]
def n131Num : Poly := n131NumPart0

def n131NF : NF := ⟨n131Num,(15625 : Int)⟩
def n131QPart0 : Poly := []
def n131Q : Poly := n131QPart0

def n131Row : Row := ⟨n131NF,.add 126 130,(1 : Int),n131Q⟩

def n132NumPart0 : Poly := [(pm0, (1600 : Int))]
def n132Num : Poly := n132NumPart0

def n132NF : NF := ⟨n132Num,(1 : Int)⟩
def n132QPart0 : Poly := []
def n132Q : Poly := n132QPart0

def n132Row : Row := ⟨n132NF,.lit (1600 : Int) (1 : Int),(1 : Int),n132Q⟩

def n133NumPart0 : Poly := [(pm4, (1600 : Int))]
def n133Num : Poly := n133NumPart0

def n133NF : NF := ⟨n133Num,(1 : Int)⟩
def n133QPart0 : Poly := []
def n133Q : Poly := n133QPart0

def n133Row : Row := ⟨n133NF,.mul 9 132,(1 : Int),n133Q⟩

def n134NumPart0 : Poly := [(pm0, (2033911296 : Int)), (pm1, (-28958529024 : Int)), (pm2, (143350576128 : Int)), (pm3, (-278086459392 : Int)), (pm4, (173215412800 : Int)), (pm5, (-89940275200 : Int))]
def n134Num : Poly := n134NumPart0

def n134NF : NF := ⟨n134Num,(15625 : Int)⟩
def n134QPart0 : Poly := []
def n134Q : Poly := n134QPart0

def n134Row : Row := ⟨n134NF,.add 131 133,(1 : Int),n134Q⟩

def n135NumPart0 : Poly := [(pm0, (13561344 : Int))]
def n135Num : Poly := n135NumPart0

def n135NF : NF := ⟨n135Num,(1 : Int)⟩
def n135QPart0 : Poly := []
def n135Q : Poly := n135QPart0

def n135Row : Row := ⟨n135NF,.lit (13561344 : Int) (1 : Int),(1 : Int),n135Q⟩

def n136NumPart0 : Poly := [(pm3, (13561344 : Int))]
def n136Num : Poly := n136NumPart0

def n136NF : NF := ⟨n136Num,(1 : Int)⟩
def n136QPart0 : Poly := []
def n136Q : Poly := n136QPart0

def n136Row : Row := ⟨n136NF,.mul 4 135,(1 : Int),n136Q⟩

def n137NumPart0 : Poly := [(pm0, (-6534307584 : Int)), (pm1, (91830640896 : Int)), (pm2, (-441143488512 : Int)), (pm3, (782813011968 : Int)), (pm4, (-302549817600 : Int)), (pm5, (111443692800 : Int))]
def n137Num : Poly := n137NumPart0

def n137NF : NF := ⟨n137Num,(78125 : Int)⟩
def n137QPart0 : Poly := [(pm0, (-24503653440000 : Int)), (pm1, (1313755200000 : Int)), (pm2, (16739784000000 : Int))]
def n137Q : Poly := n137QPart0

def n137Row : Row := ⟨n137NF,.mul 18 136,(1 : Int),n137Q⟩

def n138NumPart0 : Poly := [(pm0, (6534307584 : Int)), (pm1, (-91830640896 : Int)), (pm2, (441143488512 : Int)), (pm3, (-782813011968 : Int)), (pm4, (302549817600 : Int)), (pm5, (-111443692800 : Int))]
def n138Num : Poly := n138NumPart0

def n138NF : NF := ⟨n138Num,(78125 : Int)⟩
def n138QPart0 : Poly := []
def n138Q : Poly := n138QPart0

def n138Row : Row := ⟨n138NF,.mul 13 137,(1 : Int),n138Q⟩

def n139NumPart0 : Poly := [(pm0, (16703864064 : Int)), (pm1, (-236623286016 : Int)), (pm2, (1157896369152 : Int)), (pm3, (-2173245308928 : Int)), (pm4, (1168626881600 : Int)), (pm5, (-561145068800 : Int))]
def n139Num : Poly := n139NumPart0

def n139NF : NF := ⟨n139Num,(78125 : Int)⟩
def n139QPart0 : Poly := []
def n139Q : Poly := n139QPart0

def n139Row : Row := ⟨n139NF,.add 134 138,(1 : Int),n139Q⟩

def n140NumPart0 : Poly := [(pm0, (294144 : Int))]
def n140Num : Poly := n140NumPart0

def n140NF : NF := ⟨n140Num,(1 : Int)⟩
def n140QPart0 : Poly := []
def n140Q : Poly := n140QPart0

def n140Row : Row := ⟨n140NF,.lit (294144 : Int) (1 : Int),(1 : Int),n140Q⟩

def n141NumPart0 : Poly := [(pm3, (294144 : Int))]
def n141Num : Poly := n141NumPart0

def n141NF : NF := ⟨n141Num,(1 : Int)⟩
def n141QPart0 : Poly := []
def n141Q : Poly := n141QPart0

def n141Row : Row := ⟨n141NF,.mul 4 140,(1 : Int),n141Q⟩

def n142NumPart0 : Poly := [(pm0, (12574656 : Int)), (pm1, (-139644864 : Int)), (pm2, (487396608 : Int)), (pm3, (-543578112 : Int)), (pm4, (141556800 : Int)), (pm5, (612800 : Int))]
def n142Num : Poly := n142NumPart0

def n142NF : NF := ⟨n142Num,(1875 : Int)⟩
def n142QPart0 : Poly := [(pm0, (83831040 : Int)), (pm1, (242668800 : Int)), (pm2, (992736000 : Int))]
def n142Q : Poly := n142QPart0

def n142Row : Row := ⟨n142NF,.mul 1 141,(1 : Int),n142Q⟩

def n143NumPart0 : Poly := [(pm0, (51683424192 : Int)), (pm1, (-727325466048 : Int)), (pm2, (3534613683456 : Int)), (pm3, (-6587683190784 : Int)), (pm4, (3523575244800 : Int)), (pm5, (-1683358606400 : Int))]
def n143Num : Poly := n143NumPart0

def n143NF : NF := ⟨n143Num,(234375 : Int)⟩
def n143QPart0 : Poly := []
def n143Q : Poly := n143QPart0

def n143Row : Row := ⟨n143NF,.add 139 142,(1 : Int),n143Q⟩

def n144NumPart0 : Poly := [(pm0, (18662400 : Int))]
def n144Num : Poly := n144NumPart0

def n144NF : NF := ⟨n144Num,(1 : Int)⟩
def n144QPart0 : Poly := []
def n144Q : Poly := n144QPart0

def n144Row : Row := ⟨n144NF,.lit (18662400 : Int) (1 : Int),(1 : Int),n144Q⟩

def n145NumPart0 : Poly := [(pm2, (18662400 : Int))]
def n145Num : Poly := n145NumPart0

def n145NF : NF := ⟨n145Num,(1 : Int)⟩
def n145QPart0 : Poly := []
def n145Q : Poly := n145QPart0

def n145Row : Row := ⟨n145NF,.mul 3 144,(1 : Int),n145Q⟩

def n146NumPart0 : Poly := [(pm0, (-1150799616 : Int)), (pm1, (16097128704 : Int)), (pm2, (-77650188288 : Int)), (pm3, (145050488832 : Int)), (pm4, (-92149920000 : Int)), (pm5, (76320275200 : Int))]
def n146Num : Poly := n146NumPart0

def n146NF : NF := ⟨n146Num,(78125 : Int)⟩
def n146QPart0 : Poly := [(pm0, (-9709871760000000 : Int)), (pm1, (-118681200000000 : Int))]
def n146Q : Poly := n146QPart0

def n146Row : Row := ⟨n146NF,.mul 28 145,(1 : Int),n146Q⟩

def n147NumPart0 : Poly := [(pm0, (48231025344 : Int)), (pm1, (-679034079936 : Int)), (pm2, (3301663118592 : Int)), (pm3, (-6152531724288 : Int)), (pm4, (3247125484800 : Int)), (pm5, (-1454397780800 : Int))]
def n147Num : Poly := n147NumPart0

def n147NF : NF := ⟨n147Num,(234375 : Int)⟩
def n147QPart0 : Poly := []
def n147Q : Poly := n147QPart0

def n147Row : Row := ⟨n147NF,.add 143 146,(1 : Int),n147Q⟩

def n148NumPart0 : Poly := [(pm0, (6708096 : Int))]
def n148Num : Poly := n148NumPart0

def n148NF : NF := ⟨n148Num,(1 : Int)⟩
def n148QPart0 : Poly := []
def n148Q : Poly := n148QPart0

def n148Row : Row := ⟨n148NF,.lit (6708096 : Int) (1 : Int),(1 : Int),n148Q⟩

def n149NumPart0 : Poly := [(pm2, (6708096 : Int))]
def n149Num : Poly := n149NumPart0

def n149NF : NF := ⟨n149Num,(1 : Int)⟩
def n149QPart0 : Poly := []
def n149Q : Poly := n149QPart0

def n149Row : Row := ⟨n149NF,.mul 3 148,(1 : Int),n149Q⟩

def n150NumPart0 : Poly := [(pm0, (34658496 : Int)), (pm1, (-43602624 : Int)), (pm2, (-2140131072 : Int)), (pm3, (8495927808 : Int)), (pm4, (-4537281600 : Int)), (pm5, (-2992763200 : Int))]
def n150Num : Poly := n150NumPart0

def n150NF : NF := ⟨n150Num,(15625 : Int)⟩
def n150QPart0 : Poly := [(pm0, (129969360000 : Int)), (pm1, (1656061200000 : Int))]
def n150Q : Poly := n150QPart0

def n150Row : Row := ⟨n150NF,.mul 18 149,(1 : Int),n150Q⟩

def n151NumPart0 : Poly := [(pm0, (48750902784 : Int)), (pm1, (-679688119296 : Int)), (pm2, (3269561152512 : Int)), (pm3, (-6025092807168 : Int)), (pm4, (3179066260800 : Int)), (pm5, (-1499289228800 : Int))]
def n151Num : Poly := n151NumPart0

def n151NF : NF := ⟨n151Num,(234375 : Int)⟩
def n151QPart0 : Poly := []
def n151Q : Poly := n151QPart0

def n151Row : Row := ⟨n151NF,.add 147 150,(1 : Int),n151Q⟩

def n152NumPart0 : Poly := [(pm0, (23040 : Int))]
def n152Num : Poly := n152NumPart0

def n152NF : NF := ⟨n152Num,(1 : Int)⟩
def n152QPart0 : Poly := []
def n152Q : Poly := n152QPart0

def n152Row : Row := ⟨n152NF,.lit (23040 : Int) (1 : Int),(1 : Int),n152Q⟩

def n153NumPart0 : Poly := [(pm2, (23040 : Int))]
def n153Num : Poly := n153NumPart0

def n153NF : NF := ⟨n153Num,(1 : Int)⟩
def n153QPart0 : Poly := []
def n153Q : Poly := n153QPart0

def n153Row : Row := ⟨n153NF,.mul 3 152,(1 : Int),n153Q⟩

def n154NumPart0 : Poly := [(pm0, (38016 : Int)), (pm1, (-376704 : Int)), (pm2, (1049088 : Int)), (pm3, (-632832 : Int)), (pm4, (316800 : Int)), (pm5, (60800 : Int))]
def n154Num : Poly := n154NumPart0

def n154NF : NF := ⟨n154Num,(25 : Int)⟩
def n154QPart0 : Poly := [(pm0, (253440 : Int)), (pm1, (1036800 : Int))]
def n154Q : Poly := n154QPart0

def n154Row : Row := ⟨n154NF,.mul 1 153,(1 : Int),n154Q⟩

def n155NumPart0 : Poly := [(pm0, (-38016 : Int)), (pm1, (376704 : Int)), (pm2, (-1049088 : Int)), (pm3, (632832 : Int)), (pm4, (-316800 : Int)), (pm5, (-60800 : Int))]
def n155Num : Poly := n155NumPart0

def n155NF : NF := ⟨n155Num,(25 : Int)⟩
def n155QPart0 : Poly := []
def n155Q : Poly := n155QPart0

def n155Row : Row := ⟨n155NF,.mul 13 154,(1 : Int),n155Q⟩

def n156NumPart0 : Poly := [(pm0, (48394502784 : Int)), (pm1, (-676156519296 : Int)), (pm2, (3259725952512 : Int)), (pm3, (-6019160007168 : Int)), (pm4, (3176096260800 : Int)), (pm5, (-1499859228800 : Int))]
def n156Num : Poly := n156NumPart0

def n156NF : NF := ⟨n156Num,(234375 : Int)⟩
def n156QPart0 : Poly := []
def n156Q : Poly := n156QPart0

def n156Row : Row := ⟨n156NF,.add 151 155,(1 : Int),n156Q⟩

def n157NumPart0 : Poly := [(pm0, (4665600 : Int))]
def n157Num : Poly := n157NumPart0

def n157NF : NF := ⟨n157Num,(1 : Int)⟩
def n157QPart0 : Poly := []
def n157Q : Poly := n157QPart0

def n157Row : Row := ⟨n157NF,.lit (4665600 : Int) (1 : Int),(1 : Int),n157Q⟩

def n158NumPart0 : Poly := [(pm1, (4665600 : Int))]
def n158Num : Poly := n158NumPart0

def n158NF : NF := ⟨n158Num,(1 : Int)⟩
def n158QPart0 : Poly := []
def n158Q : Poly := n158QPart0

def n158Row : Row := ⟨n158NF,.mul 0 157,(1 : Int),n158Q⟩

def n159NumPart0 : Poly := [(pm0, (-703296 : Int)), (pm1, (-1757376 : Int)), (pm2, (168713472 : Int)), (pm3, (-1187063808 : Int)), (pm4, (2430792000 : Int)), (pm5, (-266388800 : Int))]
def n159Num : Poly := n159NumPart0

def n159NF : NF := ⟨n159Num,(15625 : Int)⟩
def n159QPart0 : Poly := [(pm0, (-5934060000000 : Int))]
def n159Q : Poly := n159QPart0

def n159Row : Row := ⟨n159NF,.mul 28 158,(1 : Int),n159Q⟩

def n160NumPart0 : Poly := [(pm0, (48383953344 : Int)), (pm1, (-676182879936 : Int)), (pm2, (3262256654592 : Int)), (pm3, (-6036965964288 : Int)), (pm4, (3212558140800 : Int)), (pm5, (-1503855060800 : Int))]
def n160Num : Poly := n160NumPart0

def n160NF : NF := ⟨n160Num,(234375 : Int)⟩
def n160QPart0 : Poly := []
def n160Q : Poly := n160QPart0

def n160Row : Row := ⟨n160NF,.add 156 159,(1 : Int),n160Q⟩

def n161NumPart0 : Poly := [(pm0, (1188864 : Int))]
def n161Num : Poly := n161NumPart0

def n161NF : NF := ⟨n161Num,(1 : Int)⟩
def n161QPart0 : Poly := []
def n161Q : Poly := n161QPart0

def n161Row : Row := ⟨n161NF,.lit (1188864 : Int) (1 : Int),(1 : Int),n161Q⟩

def n162NumPart0 : Poly := [(pm1, (1188864 : Int))]
def n162Num : Poly := n162NumPart0

def n162NF : NF := ⟨n162Num,(1 : Int)⟩
def n162QPart0 : Poly := []
def n162Q : Poly := n162QPart0

def n162Row : Row := ⟨n162NF,.mul 0 161,(1 : Int),n162Q⟩

def n163NumPart0 : Poly := [(pm0, (46960128 : Int)), (pm1, (-476140032 : Int)), (pm2, (1357154304 : Int)), (pm3, (-701561856 : Int)), (pm4, (-229516800 : Int)), (pm5, (17062400 : Int))]
def n163Num : Poly := n163NumPart0

def n163NF : NF := ⟨n163Num,(9375 : Int)⟩
def n163QPart0 : Poly := [(pm0, (176100480000 : Int))]
def n163Q : Poly := n163QPart0

def n163Row : Row := ⟨n163NF,.mul 18 162,(1 : Int),n163Q⟩

def n164NumPart0 : Poly := [(pm0, (-46960128 : Int)), (pm1, (476140032 : Int)), (pm2, (-1357154304 : Int)), (pm3, (701561856 : Int)), (pm4, (229516800 : Int)), (pm5, (-17062400 : Int))]
def n164Num : Poly := n164NumPart0

def n164NF : NF := ⟨n164Num,(9375 : Int)⟩
def n164QPart0 : Poly := []
def n164Q : Poly := n164QPart0

def n164Row : Row := ⟨n164NF,.mul 13 163,(1 : Int),n164Q⟩

def n165NumPart0 : Poly := [(pm0, (47209950144 : Int)), (pm1, (-664279379136 : Int)), (pm2, (3228327796992 : Int)), (pm3, (-6019426917888 : Int)), (pm4, (3218296060800 : Int)), (pm5, (-1504281620800 : Int))]
def n165Num : Poly := n165NumPart0

def n165NF : NF := ⟨n165Num,(234375 : Int)⟩
def n165QPart0 : Poly := []
def n165Q : Poly := n165QPart0

def n165Row : Row := ⟨n165NF,.add 160 164,(1 : Int),n165Q⟩

def n166NumPart0 : Poly := [(pm0, (17496000 : Int))]
def n166Num : Poly := n166NumPart0

def n166NF : NF := ⟨n166Num,(1 : Int)⟩
def n166QPart0 : Poly := []
def n166Q : Poly := n166QPart0

def n166Row : Row := ⟨n166NF,.lit (17496000 : Int) (1 : Int),(1 : Int),n166Q⟩

def n167NumPart0 : Poly := [(pm0, (38442816 : Int)), (pm1, (-528379200 : Int)), (pm2, (2458804992 : Int)), (pm3, (-4094446080 : Int)), (pm4, (1087506432 : Int)), (pm5, (-323604160 : Int))]
def n167Num : Poly := n167NumPart0

def n167NF : NF := ⟨n167Num,(9375 : Int)⟩
def n167QPart0 : Poly := []
def n167Q : Poly := n167QPart0

def n167Row : Row := ⟨n167NF,.mul 45 166,(1 : Int),n167Q⟩

def n168NumPart0 : Poly := [(pm0, (-38442816 : Int)), (pm1, (528379200 : Int)), (pm2, (-2458804992 : Int)), (pm3, (4094446080 : Int)), (pm4, (-1087506432 : Int)), (pm5, (323604160 : Int))]
def n168Num : Poly := n168NumPart0

def n168NF : NF := ⟨n168Num,(9375 : Int)⟩
def n168QPart0 : Poly := []
def n168Q : Poly := n168QPart0

def n168Row : Row := ⟨n168NF,.mul 13 167,(1 : Int),n168Q⟩

def n169NumPart0 : Poly := [(pm0, (15416293248 : Int)), (pm1, (-217023299712 : Int)), (pm2, (1055619224064 : Int)), (pm3, (-1972355255296 : Int)), (pm4, (1063702800000 : Int)), (pm5, (-498730505600 : Int))]
def n169Num : Poly := n169NumPart0

def n169NF : NF := ⟨n169Num,(78125 : Int)⟩
def n169QPart0 : Poly := []
def n169Q : Poly := n169QPart0

def n169Row : Row := ⟨n169NF,.add 165 168,(1 : Int),n169Q⟩

def n170NumPart0 : Poly := [(pm0, (1700352 : Int))]
def n170Num : Poly := n170NumPart0

def n170NF : NF := ⟨n170Num,(1 : Int)⟩
def n170QPart0 : Poly := []
def n170Q : Poly := n170QPart0

def n170Row : Row := ⟨n170NF,.lit (1700352 : Int) (1 : Int),(1 : Int),n170Q⟩

def n171NumPart0 : Poly := [(pm0, (-190297728 : Int)), (pm1, (3544808832 : Int)), (pm2, (-20887816704 : Int)), (pm3, (40550624256 : Int)), (pm4, (-4646448000 : Int)), (pm5, (-53398400 : Int))]
def n171Num : Poly := n171NumPart0

def n171NF : NF := ⟨n171Num,(703125 : Int)⟩
def n171QPart0 : Poly := []
def n171Q : Poly := n171QPart0

def n171Row : Row := ⟨n171NF,.mul 28 170,(1 : Int),n171Q⟩

def n172NumPart0 : Poly := [(pm0, (190297728 : Int)), (pm1, (-3544808832 : Int)), (pm2, (20887816704 : Int)), (pm3, (-40550624256 : Int)), (pm4, (4646448000 : Int)), (pm5, (53398400 : Int))]
def n172Num : Poly := n172NumPart0

def n172NF : NF := ⟨n172Num,(703125 : Int)⟩
def n172QPart0 : Poly := []
def n172Q : Poly := n172QPart0

def n172Row : Row := ⟨n172NF,.mul 13 171,(1 : Int),n172Q⟩

def n173NumPart0 : Poly := [(pm0, (27787387392 : Int)), (pm1, (-391350901248 : Int)), (pm2, (1904292166656 : Int)), (pm3, (-3558349584384 : Int)), (pm4, (1915594329600 : Int)), (pm5, (-897704230400 : Int))]
def n173Num : Poly := n173NumPart0

def n173NF : NF := ⟨n173Num,(140625 : Int)⟩
def n173QPart0 : Poly := []
def n173Q : Poly := n173QPart0

def n173Row : Row := ⟨n173NF,.add 169 172,(1 : Int),n173Q⟩

def n174NumPart0 : Poly := [(pm0, (82944 : Int))]
def n174Num : Poly := n174NumPart0

def n174NF : NF := ⟨n174Num,(1 : Int)⟩
def n174QPart0 : Poly := []
def n174Q : Poly := n174QPart0

def n174Row : Row := ⟨n174NF,.lit (82944 : Int) (1 : Int),(1 : Int),n174Q⟩

def n175NumPart0 : Poly := [(pm0, (843264 : Int)), (pm1, (-8418816 : Int)), (pm2, (23626752 : Int)), (pm3, (-14051328 : Int)), (pm4, (5337600 : Int)), (pm5, (1011200 : Int))]
def n175Num : Poly := n175NumPart0

def n175NF : NF := ⟨n175Num,(625 : Int)⟩
def n175QPart0 : Poly := []
def n175Q : Poly := n175QPart0

def n175Row : Row := ⟨n175NF,.mul 18 174,(1 : Int),n175Q⟩

def n176NumPart0 : Poly := [(pm0, (27977121792 : Int)), (pm1, (-393245134848 : Int)), (pm2, (1909608185856 : Int)), (pm3, (-3561511133184 : Int)), (pm4, (1916795289600 : Int)), (pm5, (-897476710400 : Int))]
def n176Num : Poly := n176NumPart0

def n176NF : NF := ⟨n176Num,(140625 : Int)⟩
def n176QPart0 : Poly := []
def n176Q : Poly := n176QPart0

def n176Row : Row := ⟨n176NF,.add 173 175,(1 : Int),n176Q⟩

def n177NumPart0 : Poly := [(pm0, (-541508040364032 : Int)), (pm1, (7661439640977408 : Int)), (pm2, (-37654574059954176 : Int)), (pm3, (72199065264881664 : Int)), (pm4, (-42636182059929600 : Int)), (pm5, (18838912298598400 : Int))]
def n177Num : Poly := n177NumPart0

def n177NF : NF := ⟨n177Num,(889892578125 : Int)⟩
def n177QPart0 : Poly := []
def n177Q : Poly := n177QPart0

def n177Row : Row := ⟨n177NF,.input 2,(1 : Int),n177Q⟩

def n178NumPart0 : Poly := [(pm0, (-555271483392 : Int)), (pm1, (7887409717248 : Int)), (pm2, (-39056291782656 : Int)), (pm3, (76231909392384 : Int)), (pm4, (-47896999833600 : Int)), (pm5, (21317073510400 : Int))]
def n178Num : Poly := n178NumPart0

def n178NF : NF := ⟨n178Num,(158203125 : Int)⟩
def n178QPart0 : Poly := []
def n178Q : Poly := n178QPart0

def n178Row : Row := ⟨n178NF,.input 3,(1 : Int),n178Q⟩

def n179NumPart0 : Poly := [(pm0, (27977121792 : Int)), (pm1, (-393245134848 : Int)), (pm2, (1909608185856 : Int)), (pm3, (-3561511133184 : Int)), (pm4, (1916795289600 : Int)), (pm5, (-897476710400 : Int))]
def n179Num : Poly := n179NumPart0

def n179NF : NF := ⟨n179Num,(140625 : Int)⟩
def n179QPart0 : Poly := []
def n179Q : Poly := n179QPart0

def n179Row : Row := ⟨n179NF,.input 4,(1 : Int),n179Q⟩

def n180NumPart0 : Poly := [(pm0, (-3146067 : Int)), (pm1, (30206310 : Int)), (pm2, (-78098226 : Int)), (pm3, (37868220 : Int)), (pm4, (-17607475 : Int)), (pm5, (-3249250 : Int))]
def n180Num : Poly := n180NumPart0

def n180NF : NF := ⟨n180Num,(200 : Int)⟩
def n180QPart0 : Poly := []
def n180Q : Poly := n180QPart0

def n180Row : Row := ⟨n180NF,.input 5,(1 : Int),n180Q⟩

def n181NumPart0 : Poly := [(pm0, (-555271483392 : Int)), (pm1, (7887409717248 : Int)), (pm2, (-39056291782656 : Int)), (pm3, (76231909392384 : Int)), (pm4, (-47896999833600 : Int)), (pm5, (21317073510400 : Int))]
def n181Num : Poly := n181NumPart0

def n181NF : NF := ⟨n181Num,(158203125 : Int)⟩
def n181QPart0 : Poly := [(pm0, (-9985812049469326536000000000 : Int)), (pm1, (97323058051362466560000000000 : Int)), (pm2, (-262167703794348601608000000000 : Int)), (pm3, (158372824204166814000000000000 : Int)), (pm4, (-77471862479435764800000000000 : Int))]
def n181Q : Poly := n181QPart0

def n181Row : Row := ⟨n181NF,.mul 177 180,(1 : Int),n181Q⟩

def n182NumPart0 : Poly := [(pm0, (-382675183512658108052602582204416 : Int)), (pm1, (5408874554685506285168765492527104 : Int)), (pm2, (-26536132649443478139737869268287488 : Int)), (pm3, (50677358568412139018707646684332032 : Int)), (pm4, (-29557676248854336652250062415462400 : Int)), (pm5, (13184350013018134703086048064307200 : Int))]
def n182Num : Poly := n182NumPart0

def n182NF : NF := ⟨n182Num,(3128528594970703125 : Int)⟩
def n182QPart0 : Poly := [(pm0, (-1773643065611263481907798773760000000000000000000 : Int)), (pm1, (238308623938074153309567796800000000000000000000 : Int)), (pm2, (-31901955710446163803829616000000000000000000000 : Int)), (pm3, (4061937389341007845643688000000000000000000000 : Int)), (pm4, (-423164403264862581351840000000000000000000000 : Int))]
def n182Q : Poly := n182QPart0

def n182Row : Row := ⟨n182NF,.mul 60 176,(1 : Int),n182Q⟩

def n183NumPart0 : Poly := [(pm0, (10284397101658554486465868333056 : Int)), (pm1, (-145363498951285148215801244811264 : Int)), (pm2, (713158306304090387690781312811008 : Int)), (pm3, (-1361952512453709823602404005773312 : Int)), (pm4, (794359859764902716660234217062400 : Int)), (pm5, (-354328873622831581530187576115200 : Int))]
def n183Num : Poly := n183NumPart0

def n183NF : NF := ⟨n183Num,(625705718994140625 : Int)⟩
def n183QPart0 : Poly := [(pm0, (9533335199813940467727680832000000000000000000 : Int)), (pm1, (-1280915510900698101229925760000000000000000000 : Int)), (pm2, (171618704980408792864987200000000000000000000 : Int)), (pm3, (-22049966509773872974905600000000000000000000 : Int)), (pm4, (2274653644421843416608000000000000000000000 : Int))]
def n183Q : Poly := n183QPart0

def n183Row : Row := ⟨n183NF,.mul 116 116,(1 : Int),n183Q⟩

def n184NumPart0 : Poly := [(pm0, (-382675183512658108052602582204416 : Int)), (pm1, (5408874554685506285168765492527104 : Int)), (pm2, (-26536132649443478139737869268287488 : Int)), (pm3, (50677358568412139018707646684332032 : Int)), (pm4, (-29557676248854336652250062415462400 : Int)), (pm5, (13184350013018134703086048064307200 : Int))]
def n184Num : Poly := n184NumPart0

def n184NF : NF := ⟨n184Num,(3128528594970703125 : Int)⟩
def n184QPart0 : Poly := [(pm0, (-8868224105222312951734774348800000000000000000000 : Int))]
def n184Q : Poly := n184QPart0

def n184Row : Row := ⟨n184NF,.mul 0 183,(1 : Int),n184Q⟩

def n185NumPart0 : Poly := [(pm0, (-26531948034 : Int)), (pm1, (252981694395 : Int)), (pm2, (-655898544252 : Int)), (pm3, (317958438690 : Int)), (pm4, (-148010269950 : Int)), (pm5, (-27305164125 : Int))]
def n185Num : Poly := n185NumPart0

def n185NF : NF := ⟨n185Num,(2500 : Int)⟩
def n185QPart0 : Poly := [(pm0, (-955763771947500 : Int)), (pm1, (4592442125685000 : Int)), (pm2, (-2200413221137500 : Int)), (pm3, (1190450467250000 : Int)), (pm4, (211152511250000 : Int))]
def n185Q : Poly := n185QPart0

def n185Row : Row := ⟨n185NF,.mul 180 180,(1 : Int),n185Q⟩

def n186NumPart0 : Poly := [(pm0, (-680632210345347 : Int)), (pm1, (6486411994211160 : Int)), (pm2, (-16856900072152866 : Int)), (pm3, (8170656787856520 : Int)), (pm4, (-3806833043891475 : Int)), (pm5, (-702121619988000 : Int))]
def n186Num : Poly := n186NumPart0

def n186NF : NF := ⟨n186Num,(125000 : Int)⟩
def n186QPart0 : Poly := [(pm0, (-399045439800294750000 : Int)), (pm1, (1928527062869640375000 : Int)), (pm2, (-923657961016676250000 : Int)), (pm3, (500346580764459375000 : Int)), (pm4, (88721304533156250000 : Int))]
def n186Q : Poly := n186QPart0

def n186Row : Row := ⟨n186NF,.mul 180 185,(1 : Int),n186Q⟩

def n187NumPart0 : Poly := [(pm0, (-465464203128671298630475554 : Int)), (pm1, (4447423076241279555457081245 : Int)), (pm2, (-11614062849514512903274228812 : Int)), (pm3, (5628352501547197771675389390 : Int)), (pm4, (-2626904259371667780937255950 : Int)), (pm5, (-484268525908426804101712875 : Int))]
def n187Num : Poly := n187NumPart0

def n187NF : NF := ⟨n187Num,(976562500 : Int)⟩
def n187QPart0 : Poly := [(pm0, (-17025015661518063677339849510742187500 : Int)), (pm1, (83585567590630947990050130755859375000 : Int)), (pm2, (-39996247578943759739269273784179687500 : Int)), (pm3, (21736334120922507558600435937500000000 : Int)), (pm4, (3851365384801355321251125000000000000 : Int))]
def n187Q : Poly := n187QPart0

def n187Row : Row := ⟨n187NF,.mul 186 186,(1 : Int),n187Q⟩

def n188NumPart0 : Poly := [(pm0, (-9798707053832821955419401006507 : Int)), (pm1, (93701007085175779462031497193460 : Int)), (pm2, (-244942986627715167729642025247346 : Int)), (pm3, (118698960893725816707368204547120 : Int)), (pm4, (-55420087797858891659449383704475 : Int)), (pm5, (-10215652893362525605362249190500 : Int))]
def n188Num : Poly := n188NumPart0

def n188NF : NF := ⟨n188Num,(48828125000 : Int)⟩
def n188QPart0 : Poly := [(pm0, (-2719141343604855349917104200615136718750000 : Int)), (pm1, (13340171900522859699650557180850244140625000 : Int)), (pm2, (-6384811431124110504267365802402832031250000 : Int)), (pm3, (3468736401320897912100873004683837890625000 : Int)), (pm4, (614652151487482731729488499645996093750000 : Int))]
def n188Q : Poly := n188QPart0

def n188Row : Row := ⟨n188NF,.mul 180 187,(1 : Int),n188Q⟩

def n189NumPart0 : Poly := [(pm0, (-58073589943665415868343704473073079913733255631067748345394 : Int)), (pm1, (556849769610847981851262504136149894302062162158503206028945 : Int)), (pm2, (-1460197537456080344733108416784575382682471828460471073952332 : Int)), (pm3, (707537329997939285083685163024908231912360406581643414158790 : Int)), (pm4, (-330708020142542470731576301025288268041194753802473585117950 : Int)), (pm5, (-60941550962024050859915378253038289717349321194571615260375 : Int))]
def n189Num : Poly := n189NumPart0

def n189NF : NF := ⟨n189Num,(149011611938476562500 : Int)⟩
def n189QPart0 : Poly := [(pm0, (-535028054570333539338629356755088013763084920560464641727050989866256713867187500 : Int)), (pm1, (2693209997725880635624302419902385177549476392935361188175549209117889404296875000 : Int)), (pm2, (-1287357778516747880059375438054902660234270800504733472905629128217697143554687500 : Int)), (pm3, (702899727260280657294191082775078873396194647680278792912572622299194335937500000 : Int)), (pm4, (124406294867594410118511079938864387836485826946518308270275592803955078125000000 : Int))]
def n189Q : Poly := n189QPart0

def n189Row : Row := ⟨n189NF,.mul 188 188,(1 : Int),n189Q⟩

def n190NumPart0 : Poly := [(pm0, (-1177173045119133521811278133095273908079144913036246562661107227 : Int)), (pm1, (11289140947053433371929924097298099956414898940203180625389410060 : Int)), (pm2, (-29607461598037451788552475336973796740112955149129336762313911506 : Int)), (pm3, (14346197214581533780542072309912958210490473604271227426974672320 : Int)), (pm4, (-6705875643654508354903678147635921538299319545936349366560950475 : Int)), (pm5, (-1235713750433680597673746891245623982952052913677393829353695500 : Int))]
def n190Num : Poly := n190NumPart0

def n190NF : NF := ⟨n190Num,(7450580596923828125000 : Int)⟩
def n190QPart0 : Poly := [(pm0, (-51715886447654321787511194699580112247907348803792674255700325056910514831542968750000 : Int)), (pm1, (255930961706270577542715186098981615776818843086297536537845230050384998321533203125000 : Int)), (pm2, (-122450840137583815584178082462793813499014239725852057916362842991948127746582031250000 : Int)), (pm3, (66632350102887510192695057291458428995640958974210958436152237839996814727783203125000 : Int)), (pm4, (11802574066123762563263180422108451298719482534614909940050451084971427917480468750000 : Int))]
def n190Q : Poly := n190QPart0

def n190Row : Row := ⟨n190NF,.mul 180 189,(1 : Int),n190Q⟩

def n191NumPart0 : Poly := [(pm0, (8117215919754745195534857882122059776 : Int)), (pm1, (-114731771413670641425077943920643538944 : Int)), (pm2, (562878167129343390747639793372750675968 : Int)), (pm3, (-1074956067753988422095433597672858058752 : Int)), (pm4, (626970329224925593179743593674729062400 : Int)), (pm5, (-279663459132269102335325249375253299200 : Int))]
def n191Num : Poly := n191NumPart0

def n191NF : NF := ⟨n191Num,(19797720015048980712890625 : Int)⟩
def n191QPart0 : Poly := [(pm0, (238077367330952138653983986464535325000000000000000000000000 : Int)), (pm1, (-31988532192669004193083670465027250000000000000000000000000 : Int)), (pm2, (4283470260923889718132884558748125000000000000000000000000 : Int)), (pm3, (-546724744100094326524203542085000000000000000000000000000 : Int)), (pm4, (56210417851055219020883074050000000000000000000000000000 : Int))]
def n191Q : Poly := n191QPart0

def n191Row : Row := ⟨n191NF,.mul 177 177,(1 : Int),n191Q⟩

def n192NumPart0 : Poly := [(pm0, (-54217579843964399638960334682497485872562176 : Int)), (pm1, (518404997007633475346979149913903171140321280 : Int)), (pm2, (-1349682106430269325291105001999212728578736128 : Int)), (pm3, (627227208715985549448906731198284178820956160 : Int)), (pm4, (-296820281236716747008826173836284255849676800 : Int)), (pm5, (-54658869202062559901334974258930729877504000 : Int))]
def n192Num : Poly := n192NumPart0

def n192NF : NF := ⟨n192Num,(95367431640625 : Int)⟩
def n192QPart0 : Poly := [(pm0, (33750773472776065313726924004343757569413279224088144199480275915677493590070470511568203417600000000000000000000 : Int)), (pm1, (-328206642972661802289968539599416748622431562085490680548612961760249490001014038455513713536000000000000000000000 : Int)), (pm2, (892979340113153347870135829527990286962993088620527301297394695133959618879547373326702054092800000000000000000000 : Int)), (pm3, (-531314227316743852079273643027970256825790825287857302709475983279600745159323190917494791040000000000000000000000 : Int)), (pm4, (263659654192804423950125483570847532718307927544247333359020624524794805096395333504009658880000000000000000000000 : Int))]
def n192Q : Poly := n192QPart0

def n192Row : Row := ⟨n192NF,.mul 190 191,(1 : Int),n192Q⟩

def n193NumPart0 : Poly := [(pm0, (1 : Int))]
def n193Num : Poly := n193NumPart0

def n193NF : NF := ⟨n193Num,(931322574615478515625 : Int)⟩
def n193QPart0 : Poly := []
def n193Q : Poly := n193QPart0

def n193Row : Row := ⟨n193NF,.lit (1 : Int) (931322574615478515625 : Int),(1 : Int),n193Q⟩

def n194NumPart0 : Poly := [(pm0, (-54217579843964399638960334682497485872562176 : Int)), (pm1, (518404997007633475346979149913903171140321280 : Int)), (pm2, (-1349682106430269325291105001999212728578736128 : Int)), (pm3, (627227208715985549448906731198284178820956160 : Int)), (pm4, (-296820281236716747008826173836284255849676800 : Int)), (pm5, (-54658869202062559901334974258930729877504000 : Int))]
def n194Num : Poly := n194NumPart0

def n194NF : NF := ⟨n194Num,(88817841970012523233890533447265625 : Int)⟩
def n194QPart0 : Poly := []
def n194Q : Poly := n194QPart0

def n194Row : Row := ⟨n194NF,.mul 192 193,(1 : Int),n194Q⟩

def n195NumPart0 : Poly := [(pm0, (-54217579843964399638960334682497485872562176 : Int)), (pm1, (518404997007633475346979149913903171140321280 : Int)), (pm2, (-1349682106430269325291105001999212728578736128 : Int)), (pm3, (627227208715985549448906731198284178820956160 : Int)), (pm4, (-296820281236716747008826173836284255849676800 : Int)), (pm5, (-54658869202062559901334974258930729877504000 : Int))]
def n195Num : Poly := n195NumPart0

def n195NF : NF := ⟨n195Num,(88817841970012523233890533447265625 : Int)⟩
def n195QPart0 : Poly := []
def n195Q : Poly := n195QPart0

def n195Row : Row := ⟨n195NF,.input 6,(1 : Int),n195Q⟩

def chunk000 : Array Row := #[n000Row, n001Row, n002Row, n003Row, n004Row, n005Row, n006Row, n007Row, n008Row, n009Row, n010Row, n011Row, n012Row, n013Row, n014Row, n015Row, n016Row, n017Row, n018Row, n019Row, n020Row, n021Row, n022Row, n023Row, n024Row, n025Row, n026Row, n027Row, n028Row, n029Row, n030Row, n031Row]
def chunk001 : Array Row := #[n032Row, n033Row, n034Row, n035Row, n036Row, n037Row, n038Row, n039Row, n040Row, n041Row, n042Row, n043Row, n044Row, n045Row, n046Row, n047Row, n048Row, n049Row, n050Row, n051Row, n052Row, n053Row, n054Row, n055Row, n056Row, n057Row, n058Row, n059Row, n060Row, n061Row, n062Row, n063Row]
def chunk002 : Array Row := #[n064Row, n065Row, n066Row, n067Row, n068Row, n069Row, n070Row, n071Row, n072Row, n073Row, n074Row, n075Row, n076Row, n077Row, n078Row, n079Row, n080Row, n081Row, n082Row, n083Row, n084Row, n085Row, n086Row, n087Row, n088Row, n089Row, n090Row, n091Row, n092Row, n093Row, n094Row, n095Row]
def chunk003 : Array Row := #[n096Row, n097Row, n098Row, n099Row, n100Row, n101Row, n102Row, n103Row, n104Row, n105Row, n106Row, n107Row, n108Row, n109Row, n110Row, n111Row, n112Row, n113Row, n114Row, n115Row, n116Row, n117Row, n118Row, n119Row, n120Row, n121Row, n122Row, n123Row, n124Row, n125Row, n126Row, n127Row]
def chunk004 : Array Row := #[n128Row, n129Row, n130Row, n131Row, n132Row, n133Row, n134Row, n135Row, n136Row, n137Row, n138Row, n139Row, n140Row, n141Row, n142Row, n143Row, n144Row, n145Row, n146Row, n147Row, n148Row, n149Row, n150Row, n151Row, n152Row, n153Row, n154Row, n155Row, n156Row, n157Row, n158Row, n159Row]
def chunk005 : Array Row := #[n160Row, n161Row, n162Row, n163Row, n164Row, n165Row, n166Row, n167Row, n168Row, n169Row, n170Row, n171Row, n172Row, n173Row, n174Row, n175Row, n176Row, n177Row, n178Row, n179Row, n180Row, n181Row, n182Row, n183Row, n184Row, n185Row, n186Row, n187Row, n188Row, n189Row, n190Row, n191Row]
def chunk006 : Array Row := #[n192Row, n193Row, n194Row, n195Row]
def chunks : Array (Array Row) := #[chunk000, chunk001, chunk002, chunk003, chunk004, chunk005, chunk006]
def inputRows : Array NF := #[input0NF, input1NF, input2NF, input3NF, input4NF, input5NF, input6NF]
def defaultNF : NF := ⟨[],1⟩
def defaultRow : Row := ⟨defaultNF,.lit 0 1,1,[]⟩
def rowAt (i : Nat) : Row := (chunks.getD (i/32) #[]).getD (i%32) defaultRow
def program : Table := ⟨196,7,rowAt,(fun j => inputRows.getD j defaultNF),factorData⟩
end N6.Even.ProgramData
