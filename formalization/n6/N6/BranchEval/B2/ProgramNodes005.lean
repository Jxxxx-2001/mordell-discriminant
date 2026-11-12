import N6.BranchEval.B2.ProgramInputs

set_option maxRecDepth 64000
set_option maxHeartbeats 6000000

namespace N6.BranchEval.B2.ProgramData
open N6.SparseCheck N6.BranchEval.Program

def n0640NumPart0 : Poly := [(pm0, (6524928 : Int)), (pm1, (228837312 : Int))]
def n0640Num : Poly := n0640NumPart0

def n0640NF : NF := ⟨n0640Num, (65 : Int)⟩

def n0640QPart0 : Poly := [(pm0, (6626880 : Int))]
def n0640Q : Poly := n0640QPart0

def n0640Row : Row := ⟨n0640NF, .mul 16 639, (1 : Int), n0640Q⟩

def n0641NumPart0 : Poly := [(pm0, (2628413015699456 : Int)), (pm1, (92168928934818624 : Int))]
def n0641Num : Poly := n0641NumPart0

def n0641NF : NF := ⟨n0641Num, (9871875 : Int)⟩

def n0641QPart0 : Poly := [(pm0, (3157765183306716840000 : Int))]
def n0641Q : Poly := n0641QPart0

def n0641Row : Row := ⟨n0641NF, .mul 40 640, (1 : Int), n0641Q⟩

def n0642NumPart0 : Poly := [(pm0, (404348463250714624 : Int)), (pm1, (14179036761590181696 : Int))]
def n0642Num : Poly := n0642NumPart0

def n0642NF : NF := ⟨n0642Num, (246796875 : Int)⟩

def n0642QPart0 : Poly := [(pm0, (505488969626895891000000 : Int))]
def n0642Q : Poly := n0642QPart0

def n0642Row : Row := ⟨n0642NF, .mul 2 641, (1 : Int), n0642Q⟩

def n0643NumPart0 : Poly := [(pm0, (4279144858613476352 : Int)), (pm1, (150054118595340589008 : Int))]
def n0643Num : Poly := n0643NumPart0

def n0643NF : NF := ⟨n0643Num, (740390625 : Int)⟩

def n0643QPart0 : Poly := []
def n0643Q : Poly := n0643QPart0

def n0643Row : Row := ⟨n0643NF, .add 637 642, (1 : Int), n0643Q⟩

def n0644NumPart0 : Poly := [(pm0, (92016 : Int))]
def n0644Num : Poly := n0644NumPart0

def n0644NF : NF := ⟨n0644Num, (1 : Int)⟩

def n0644QPart0 : Poly := []
def n0644Q : Poly := n0644QPart0

def n0644Row : Row := ⟨n0644NF, .lit (92016 : Int) (1 : Int), (1 : Int), n0644Q⟩

def n0645NumPart0 : Poly := [(pm1, (92016 : Int))]
def n0645Num : Poly := n0645NumPart0

def n0645NF : NF := ⟨n0645Num, (1 : Int)⟩

def n0645QPart0 : Poly := []
def n0645Q : Poly := n0645QPart0

def n0645Row : Row := ⟨n0645NF, .mul 0 644, (1 : Int), n0645Q⟩

def n0646NumPart0 : Poly := [(pm0, (115817472 : Int)), (pm1, (4061862288 : Int))]
def n0646Num : Poly := n0646NumPart0

def n0646NF : NF := ⟨n0646Num, (325 : Int)⟩

def n0646QPart0 : Poly := [(pm0, (117627120 : Int))]
def n0646Q : Poly := n0646QPart0

def n0646Row : Row := ⟨n0646NF, .mul 16 645, (1 : Int), n0646Q⟩

def n0647NumPart0 : Poly := [(pm0, (46654331028665344 : Int)), (pm1, (1635998488593030576 : Int))]
def n0647Num : Poly := n0647NumPart0

def n0647NF : NF := ⟨n0647Num, (49359375 : Int)⟩

def n0647QPart0 : Poly := [(pm0, (280251660018471119550000 : Int))]
def n0647Q : Poly := n0647QPart0

def n0647Row : Row := ⟨n0647NF, .mul 40 646, (1 : Int), n0647Q⟩

def n0648NumPart0 : Poly := [(pm0, (-46654331028665344 : Int)), (pm1, (-1635998488593030576 : Int))]
def n0648Num : Poly := n0648NumPart0

def n0648NF : NF := ⟨n0648Num, (49359375 : Int)⟩

def n0648QPart0 : Poly := []
def n0648Q : Poly := n0648QPart0

def n0648Row : Row := ⟨n0648NF, .mul 4 647, (1 : Int), n0648Q⟩

def n0649NumPart0 : Poly := [(pm0, (275333068706422784 : Int)), (pm1, (9654933943572702336 : Int))]
def n0649Num : Poly := n0649NumPart0

def n0649NF : NF := ⟨n0649Num, (56953125 : Int)⟩

def n0649QPart0 : Poly := []
def n0649Q : Poly := n0649QPart0

def n0649Row : Row := ⟨n0649NF, .add 643 648, (1 : Int), n0649Q⟩

def n0650NumPart0 : Poly := [(pm0, (13680 : Int))]
def n0650Num : Poly := n0650NumPart0

def n0650NF : NF := ⟨n0650Num, (1 : Int)⟩

def n0650QPart0 : Poly := []
def n0650Q : Poly := n0650QPart0

def n0650Row : Row := ⟨n0650NF, .lit (13680 : Int) (1 : Int), (1 : Int), n0650Q⟩

def n0651NumPart0 : Poly := [(pm1, (13680 : Int))]
def n0651Num : Poly := n0651NumPart0

def n0651NF : NF := ⟨n0651Num, (1 : Int)⟩

def n0651QPart0 : Poly := []
def n0651Q : Poly := n0651QPart0

def n0651Row : Row := ⟨n0651NF, .mul 0 650, (1 : Int), n0651Q⟩

def n0652NumPart0 : Poly := [(pm0, (3443712 : Int)), (pm1, (120775248 : Int))]
def n0652Num : Poly := n0652NumPart0

def n0652NF : NF := ⟨n0652Num, (65 : Int)⟩

def n0652QPart0 : Poly := [(pm0, (3497520 : Int))]
def n0652Q : Poly := n0652QPart0

def n0652Row : Row := ⟨n0652NF, .mul 16 651, (1 : Int), n0652Q⟩

def n0653NumPart0 : Poly := [(pm0, (-359168052224 : Int)), (pm1, (-12594723222096 : Int))]
def n0653Num : Poly := n0653NumPart0

def n0653NF : NF := ⟨n0653Num, (131625 : Int)⟩

def n0653QPart0 : Poly := [(pm0, (-71032955650800 : Int))]
def n0653Q : Poly := n0653QPart0

def n0653Row : Row := ⟨n0653NF, .mul 3 652, (1 : Int), n0653Q⟩

def n0654NumPart0 : Poly := [(pm0, (-8500061578333184 : Int)), (pm1, (-298066387160313936 : Int))]
def n0654Num : Poly := n0654NumPart0

def n0654NF : NF := ⟨n0654Num, (82265625 : Int)⟩

def n0654QPart0 : Poly := [(pm0, (-1772904086060357250000 : Int))]
def n0654Q : Poly := n0654QPart0

def n0654Row : Row := ⟨n0654NF, .mul 10 653, (1 : Int), n0654Q⟩

def n0655NumPart0 : Poly := [(pm0, (8500061578333184 : Int)), (pm1, (298066387160313936 : Int))]
def n0655Num : Poly := n0655NumPart0

def n0655NF : NF := ⟨n0655Num, (82265625 : Int)⟩

def n0655QPart0 : Poly := []
def n0655Q : Poly := n0655QPart0

def n0655Row : Row := ⟨n0655NF, .mul 4 654, (1 : Int), n0655Q⟩

def n0656NumPart0 : Poly := [(pm0, (3655830447388494848 : Int)), (pm1, (128196738750887955792 : Int))]
def n0656Num : Poly := n0656NumPart0

def n0656NF : NF := ⟨n0656Num, (740390625 : Int)⟩

def n0656QPart0 : Poly := []
def n0656Q : Poly := n0656QPart0

def n0656Row : Row := ⟨n0656NF, .add 649 655, (1 : Int), n0656Q⟩

def n0657NumPart0 : Poly := [(pm0, (8352 : Int))]
def n0657Num : Poly := n0657NumPart0

def n0657NF : NF := ⟨n0657Num, (1 : Int)⟩

def n0657QPart0 : Poly := []
def n0657Q : Poly := n0657QPart0

def n0657Row : Row := ⟨n0657NF, .lit (8352 : Int) (1 : Int), (1 : Int), n0657Q⟩

def n0658NumPart0 : Poly := [(pm1, (8352 : Int))]
def n0658Num : Poly := n0658NumPart0

def n0658NF : NF := ⟨n0658Num, (1 : Int)⟩

def n0658QPart0 : Poly := []
def n0658Q : Poly := n0658QPart0

def n0658Row : Row := ⟨n0658NF, .mul 0 657, (1 : Int), n0658Q⟩

def n0659NumPart0 : Poly := [(pm0, (10512384 : Int)), (pm1, (368682336 : Int))]
def n0659Num : Poly := n0659NumPart0

def n0659NF : NF := ⟨n0659Num, (325 : Int)⟩

def n0659QPart0 : Poly := [(pm0, (10676640 : Int))]
def n0659Q : Poly := n0659QPart0

def n0659Row : Row := ⟨n0659NF, .mul 16 658, (1 : Int), n0659Q⟩

def n0660NumPart0 : Poly := [(pm0, (-1096407738368 : Int)), (pm1, (-38447049835872 : Int))]
def n0660Num : Poly := n0660NumPart0

def n0660NF : NF := ⟨n0660Num, (658125 : Int)⟩

def n0660QPart0 : Poly := [(pm0, (-1084187217828000 : Int))]
def n0660Q : Poly := n0660QPart0

def n0660Row : Row := ⟨n0660NF, .mul 3 659, (1 : Int), n0660Q⟩

def n0661NumPart0 : Poly := [(pm0, (-168668614223872 : Int)), (pm1, (-5914597677365088 : Int))]
def n0661Num : Poly := n0661NumPart0

def n0661NF : NF := ⟨n0661Num, (16453125 : Int)⟩

def n0661QPart0 : Poly := [(pm0, (-14057202596240700000 : Int))]
def n0661Q : Poly := n0661QPart0

def n0661Row : Row := ⟨n0661NF, .mul 2 660, (1 : Int), n0661Q⟩

def n0662NumPart0 : Poly := [(pm0, (3648240359748420608 : Int)), (pm1, (127930581855406526832 : Int))]
def n0662Num : Poly := n0662NumPart0

def n0662NF : NF := ⟨n0662Num, (740390625 : Int)⟩

def n0662QPart0 : Poly := []
def n0662Q : Poly := n0662QPart0

def n0662Row : Row := ⟨n0662NF, .add 656 661, (1 : Int), n0662Q⟩

def n0663NumPart0 : Poly := [(pm1, (96 : Int))]
def n0663Num : Poly := n0663NumPart0

def n0663NF : NF := ⟨n0663Num, (1 : Int)⟩

def n0663QPart0 : Poly := []
def n0663Q : Poly := n0663QPart0

def n0663Row : Row := ⟨n0663NF, .mul 0 492, (1 : Int), n0663Q⟩

def n0664NumPart0 : Poly := [(pm0, (120832 : Int)), (pm1, (4237728 : Int))]
def n0664Num : Poly := n0664NumPart0

def n0664NF : NF := ⟨n0664Num, (325 : Int)⟩

def n0664QPart0 : Poly := [(pm0, (122720 : Int))]
def n0664Q : Poly := n0664QPart0

def n0664Row : Row := ⟨n0664NF, .mul 16 663, (1 : Int), n0664Q⟩

def n0665NumPart0 : Poly := [(pm0, (-37807163392 : Int)), (pm1, (-1325760339168 : Int))]
def n0665Num : Poly := n0665NumPart0

def n0665NF : NF := ⟨n0665Num, (1974375 : Int)⟩

def n0665QPart0 : Poly := [(pm0, (-37385766132000 : Int))]
def n0665Q : Poly := n0665QPart0

def n0665Row : Row := ⟨n0665NF, .mul 3 664, (1 : Int), n0665Q⟩

def n0666NumPart0 : Poly := [(pm0, (37807163392 : Int)), (pm1, (1325760339168 : Int))]
def n0666Num : Poly := n0666NumPart0

def n0666NF : NF := ⟨n0666Num, (1974375 : Int)⟩

def n0666QPart0 : Poly := []
def n0666Q : Poly := n0666QPart0

def n0666Row : Row := ⟨n0666NF, .mul 4 665, (1 : Int), n0666Q⟩

def n0667NumPart0 : Poly := [(pm0, (3648254537434692608 : Int)), (pm1, (127931079015533714832 : Int))]
def n0667Num : Poly := n0667NumPart0

def n0667NF : NF := ⟨n0667Num, (740390625 : Int)⟩

def n0667QPart0 : Poly := []
def n0667Q : Poly := n0667QPart0

def n0667Row : Row := ⟨n0667NF, .add 662 666, (1 : Int), n0667Q⟩

def n0668NumPart0 : Poly := [(pm1, (288 : Int))]
def n0668Num : Poly := n0668NumPart0

def n0668NF : NF := ⟨n0668Num, (1 : Int)⟩

def n0668QPart0 : Poly := []
def n0668Q : Poly := n0668QPart0

def n0668Row : Row := ⟨n0668NF, .mul 0 567, (1 : Int), n0668Q⟩

def n0669NumPart0 : Poly := [(pm0, (362496 : Int)), (pm1, (12713184 : Int))]
def n0669Num : Poly := n0669NumPart0

def n0669NF : NF := ⟨n0669Num, (325 : Int)⟩

def n0669QPart0 : Poly := [(pm0, (368160 : Int))]
def n0669Q : Poly := n0669QPart0

def n0669Row : Row := ⟨n0669NF, .mul 16 668, (1 : Int), n0669Q⟩

def n0670NumPart0 : Poly := [(pm0, (8580007936 : Int)), (pm1, (300869816544 : Int))]
def n0670Num : Poly := n0670NumPart0

def n0670NF : NF := ⟨n0670Num, (203125 : Int)⟩

def n0670QPart0 : Poly := [(pm0, (4418714300000 : Int))]
def n0670Q : Poly := n0670QPart0

def n0670Row : Row := ⟨n0670NF, .mul 10 669, (1 : Int), n0670Q⟩

def n0671NumPart0 : Poly := [(pm0, (3648285811563619328 : Int)), (pm1, (127932175686015017712 : Int))]
def n0671Num : Poly := n0671NumPart0

def n0671NF : NF := ⟨n0671Num, (740390625 : Int)⟩

def n0671QPart0 : Poly := []
def n0671Q : Poly := n0671QPart0

def n0671Row : Row := ⟨n0671NF, .add 667 670, (1 : Int), n0671Q⟩

def n0672NumPart0 : Poly := [(pm0, (746496 : Int)), (pm1, (26488944 : Int))]
def n0672Num : Poly := n0672NumPart0

def n0672NF : NF := ⟨n0672Num, (65 : Int)⟩

def n0672QPart0 : Poly := [(pm0, (151632 : Int))]
def n0672Q : Poly := n0672QPart0

def n0672Row : Row := ⟨n0672NF, .mul 1 326, (1 : Int), n0672Q⟩

def n0673NumPart0 : Poly := [(pm0, (-391696659429428224 : Int)), (pm1, (-13735383804335766096 : Int))]
def n0673Num : Poly := n0673NumPart0

def n0673NF : NF := ⟨n0673Num, (246796875 : Int)⟩

def n0673QPart0 : Poly := [(pm0, (-317648765314769370036750000 : Int))]
def n0673Q : Poly := n0673QPart0

def n0673Row : Row := ⟨n0673NF, .mul 169 672, (1 : Int), n0673Q⟩

def n0674NumPart0 : Poly := [(pm0, (2473195833275334656 : Int)), (pm1, (86726024273007719424 : Int))]
def n0674Num : Poly := n0674NumPart0

def n0674NF : NF := ⟨n0674Num, (740390625 : Int)⟩

def n0674QPart0 : Poly := []
def n0674Q : Poly := n0674QPart0

def n0674Row : Row := ⟨n0674NF, .add 671 673, (1 : Int), n0674Q⟩

def n0675NumPart0 : Poly := [(pm0, (226800 : Int))]
def n0675Num : Poly := n0675NumPart0

def n0675NF : NF := ⟨n0675Num, (1 : Int)⟩

def n0675QPart0 : Poly := []
def n0675Q : Poly := n0675QPart0

def n0675Row : Row := ⟨n0675NF, .lit (226800 : Int) (1 : Int), (1 : Int), n0675Q⟩

def n0676NumPart0 : Poly := [(pm1, (226800 : Int))]
def n0676Num : Poly := n0676NumPart0

def n0676NF : NF := ⟨n0676Num, (1 : Int)⟩

def n0676QPart0 : Poly := []
def n0676Q : Poly := n0676QPart0

def n0676Row : Row := ⟨n0676NF, .mul 0 675, (1 : Int), n0676Q⟩

def n0677NumPart0 : Poly := [(pm0, (967680 : Int)), (pm1, (34337520 : Int))]
def n0677Num : Poly := n0677NumPart0

def n0677NF : NF := ⟨n0677Num, (13 : Int)⟩

def n0677QPart0 : Poly := [(pm0, (196560 : Int))]
def n0677Q : Poly := n0677QPart0

def n0677Row : Row := ⟨n0677NF, .mul 1 676, (1 : Int), n0677Q⟩

def n0678NumPart0 : Poly := [(pm0, (6067573320704 : Int)), (pm1, (212767830200016 : Int))]
def n0678Num : Poly := n0678NumPart0

def n0678NF : NF := ⟨n0678Num, (30375 : Int)⟩

def n0678QPart0 : Poly := [(pm0, (1457936331602562000 : Int))]
def n0678Q : Poly := n0678QPart0

def n0678Row : Row := ⟨n0678NF, .mul 40 677, (1 : Int), n0678Q⟩

def n0679NumPart0 : Poly := [(pm0, (1866735389640031232 : Int)), (pm1, (65459652056240592528 : Int))]
def n0679Num : Poly := n0679NumPart0

def n0679NF : NF := ⟨n0679Num, (246796875 : Int)⟩

def n0679QPart0 : Poly := [(pm0, (89851189793997381750000 : Int))]
def n0679Q : Poly := n0679QPart0

def n0679Row : Row := ⟨n0679NF, .mul 10 678, (1 : Int), n0679Q⟩

def n0680NumPart0 : Poly := [(pm0, (-1866735389640031232 : Int)), (pm1, (-65459652056240592528 : Int))]
def n0680Num : Poly := n0680NumPart0

def n0680NF : NF := ⟨n0680Num, (246796875 : Int)⟩

def n0680QPart0 : Poly := []
def n0680Q : Poly := n0680QPart0

def n0680Row : Row := ⟨n0680NF, .mul 4 679, (1 : Int), n0680Q⟩

def n0681NumPart0 : Poly := [(pm0, (-625402067128951808 : Int)), (pm1, (-21930586379142811632 : Int))]
def n0681Num : Poly := n0681NumPart0

def n0681NF : NF := ⟨n0681Num, (148078125 : Int)⟩

def n0681QPart0 : Poly := []
def n0681Q : Poly := n0681QPart0

def n0681Row : Row := ⟨n0681NF, .add 674 680, (1 : Int), n0681Q⟩

def n0682NumPart0 : Poly := [(pm0, (199584 : Int))]
def n0682Num : Poly := n0682NumPart0

def n0682NF : NF := ⟨n0682Num, (1 : Int)⟩

def n0682QPart0 : Poly := []
def n0682Q : Poly := n0682QPart0

def n0682Row : Row := ⟨n0682NF, .lit (199584 : Int) (1 : Int), (1 : Int), n0682Q⟩

def n0683NumPart0 : Poly := [(pm1, (199584 : Int))]
def n0683Num : Poly := n0683NumPart0

def n0683NF : NF := ⟨n0683Num, (1 : Int)⟩

def n0683QPart0 : Poly := []
def n0683Q : Poly := n0683QPart0

def n0683Row : Row := ⟨n0683NF, .mul 0 682, (1 : Int), n0683Q⟩

def n0684NumPart0 : Poly := [(pm0, (4257792 : Int)), (pm1, (151085088 : Int))]
def n0684Num : Poly := n0684NumPart0

def n0684NF : NF := ⟨n0684Num, (65 : Int)⟩

def n0684QPart0 : Poly := [(pm0, (864864 : Int))]
def n0684Q : Poly := n0684QPart0

def n0684Row : Row := ⟨n0684NF, .mul 1 683, (1 : Int), n0684Q⟩

def n0685NumPart0 : Poly := [(pm0, (133486613055488 : Int)), (pm1, (4680892264400352 : Int))]
def n0685Num : Poly := n0685NumPart0

def n0685NF : NF := ⟨n0685Num, (759375 : Int)⟩

def n0685QPart0 : Poly := [(pm0, (160372996476281820000 : Int))]
def n0685Q : Poly := n0685QPart0

def n0685Row : Row := ⟨n0685NF, .mul 40 684, (1 : Int), n0685Q⟩

def n0686NumPart0 : Poly := [(pm0, (266958192995608576 : Int)), (pm1, (9361257371579371104 : Int))]
def n0686Num : Poly := n0686NumPart0

def n0686NF : NF := ⟨n0686Num, (246796875 : Int)⟩

def n0686QPart0 : Poly := [(pm0, (25671768512570680500000 : Int))]
def n0686Q : Poly := n0686QPart0

def n0686Row : Row := ⟨n0686NF, .mul 2 685, (1 : Int), n0686Q⟩

def n0687NumPart0 : Poly := [(pm0, (-2326135756657933312 : Int)), (pm1, (-81569159780975944848 : Int))]
def n0687Num : Poly := n0687NumPart0

def n0687NF : NF := ⟨n0687Num, (740390625 : Int)⟩

def n0687QPart0 : Poly := []
def n0687Q : Poly := n0687QPart0

def n0687Row : Row := ⟨n0687NF, .add 681 686, (1 : Int), n0687Q⟩

def n0688NumPart0 : Poly := [(pm0, (442368 : Int)), (pm1, (15697152 : Int))]
def n0688Num : Poly := n0688NumPart0

def n0688NF : NF := ⟨n0688Num, (65 : Int)⟩

def n0688QPart0 : Poly := [(pm0, (89856 : Int))]
def n0688Q : Poly := n0688QPart0

def n0688Row : Row := ⟨n0688NF, .mul 1 615, (1 : Int), n0688Q⟩

def n0689NumPart0 : Poly := [(pm0, (13868739018752 : Int)), (pm1, (486326469028608 : Int))]
def n0689Num : Poly := n0689NumPart0

def n0689NF : NF := ⟨n0689Num, (759375 : Int)⟩

def n0689QPart0 : Poly := [(pm0, (16662129504029280000 : Int))]
def n0689Q : Poly := n0689QPart0

def n0689Row : Row := ⟨n0689NF, .mul 40 688, (1 : Int), n0689Q⟩

def n0690NumPart0 : Poly := [(pm0, (-13868739018752 : Int)), (pm1, (-486326469028608 : Int))]
def n0690Num : Poly := n0690NumPart0

def n0690NF : NF := ⟨n0690Num, (759375 : Int)⟩

def n0690QPart0 : Poly := []
def n0690Q : Poly := n0690QPart0

def n0690Row : Row := ⟨n0690NF, .mul 4 689, (1 : Int), n0690Q⟩

def n0691NumPart0 : Poly := [(pm0, (-2339657777201216512 : Int)), (pm1, (-82043328088278837648 : Int))]
def n0691Num : Poly := n0691NumPart0

def n0691NF : NF := ⟨n0691Num, (740390625 : Int)⟩

def n0691QPart0 : Poly := []
def n0691Q : Poly := n0691QPart0

def n0691Row : Row := ⟨n0691NF, .add 687 690, (1 : Int), n0691Q⟩

def n0692NumPart0 : Poly := [(pm0, (14208 : Int))]
def n0692Num : Poly := n0692NumPart0

def n0692NF : NF := ⟨n0692Num, (1 : Int)⟩

def n0692QPart0 : Poly := []
def n0692Q : Poly := n0692QPart0

def n0692Row : Row := ⟨n0692NF, .lit (14208 : Int) (1 : Int), (1 : Int), n0692Q⟩

def n0693NumPart0 : Poly := [(pm1, (14208 : Int))]
def n0693Num : Poly := n0693NumPart0

def n0693NF : NF := ⟨n0693Num, (1 : Int)⟩

def n0693QPart0 : Poly := []
def n0693Q : Poly := n0693QPart0

def n0693Row : Row := ⟨n0693NF, .mul 0 692, (1 : Int), n0693Q⟩

def n0694NumPart0 : Poly := [(pm0, (303104 : Int)), (pm1, (10755456 : Int))]
def n0694Num : Poly := n0694NumPart0

def n0694NF : NF := ⟨n0694Num, (65 : Int)⟩

def n0694QPart0 : Poly := [(pm0, (61568 : Int))]
def n0694Q : Poly := n0694QPart0

def n0694Row : Row := ⟨n0694NF, .mul 1 693, (1 : Int), n0694Q⟩

def n0695NumPart0 : Poly := [(pm0, (-95953936384 : Int)), (pm1, (-3364755140736 : Int))]
def n0695Num : Poly := n0695NumPart0

def n0695NF : NF := ⟨n0695Num, (394875 : Int)⟩

def n0695QPart0 : Poly := [(pm0, (-18977195452800 : Int))]
def n0695Q : Poly := n0695QPart0

def n0695Row : Row := ⟨n0695NF, .mul 3 694, (1 : Int), n0695Q⟩

def n0696NumPart0 : Poly := [(pm0, (-2270841955999744 : Int)), (pm1, (-79630206369538176 : Int))]
def n0696Num : Poly := n0696NumPart0

def n0696NF : NF := ⟨n0696Num, (246796875 : Int)⟩

def n0696QPart0 : Poly := [(pm0, (-1420925581072998000000 : Int))]
def n0696Q : Poly := n0696QPart0

def n0696Row : Row := ⟨n0696NF, .mul 10 695, (1 : Int), n0696Q⟩

def n0697NumPart0 : Poly := [(pm0, (2270841955999744 : Int)), (pm1, (79630206369538176 : Int))]
def n0697Num : Poly := n0697NumPart0

def n0697NF : NF := ⟨n0697Num, (246796875 : Int)⟩

def n0697QPart0 : Poly := []
def n0697Q : Poly := n0697QPart0

def n0697Row : Row := ⟨n0697NF, .mul 4 696, (1 : Int), n0697Q⟩

def n0698NumPart0 : Poly := [(pm0, (-466569050266643456 : Int)), (pm1, (-16360887493834044624 : Int))]
def n0698Num : Poly := n0698NumPart0

def n0698NF : NF := ⟨n0698Num, (148078125 : Int)⟩

def n0698QPart0 : Poly := []
def n0698Q : Poly := n0698QPart0

def n0698Row : Row := ⟨n0698NF, .add 691 697, (1 : Int), n0698Q⟩

def n0699NumPart0 : Poly := [(pm0, (1920 : Int))]
def n0699Num : Poly := n0699NumPart0

def n0699NF : NF := ⟨n0699Num, (1 : Int)⟩

def n0699QPart0 : Poly := []
def n0699Q : Poly := n0699QPart0

def n0699Row : Row := ⟨n0699NF, .lit (1920 : Int) (1 : Int), (1 : Int), n0699Q⟩

def n0700NumPart0 : Poly := [(pm1, (1920 : Int))]
def n0700Num : Poly := n0700NumPart0

def n0700NF : NF := ⟨n0700Num, (1 : Int)⟩

def n0700QPart0 : Poly := []
def n0700Q : Poly := n0700QPart0

def n0700Row : Row := ⟨n0700NF, .mul 0 699, (1 : Int), n0700Q⟩

def n0701NumPart0 : Poly := [(pm0, (8192 : Int)), (pm1, (290688 : Int))]
def n0701Num : Poly := n0701NumPart0

def n0701NF : NF := ⟨n0701Num, (13 : Int)⟩

def n0701QPart0 : Poly := [(pm0, (1664 : Int))]
def n0701Q : Poly := n0701QPart0

def n0701Row : Row := ⟨n0701NF, .mul 1 700, (1 : Int), n0701Q⟩

def n0702NumPart0 : Poly := [(pm0, (-2593349632 : Int)), (pm1, (-90939328128 : Int))]
def n0702Num : Poly := n0702NumPart0

def n0702NF : NF := ⟨n0702Num, (78975 : Int)⟩

def n0702QPart0 : Poly := [(pm0, (-102579434880 : Int))]
def n0702Q : Poly := n0702QPart0

def n0702Row : Row := ⟨n0702NF, .mul 3 701, (1 : Int), n0702Q⟩

def n0703NumPart0 : Poly := [(pm0, (-398954160128 : Int)), (pm1, (-13989878070912 : Int))]
def n0703Num : Poly := n0703NumPart0

def n0703NF : NF := ⟨n0703Num, (1974375 : Int)⟩

def n0703QPart0 : Poly := [(pm0, (-3989963021616000 : Int))]
def n0703Q : Poly := n0703QPart0

def n0703Row : Row := ⟨n0703NF, .mul 2 702, (1 : Int), n0703Q⟩

def n0704NumPart0 : Poly := [(pm0, (398954160128 : Int)), (pm1, (13989878070912 : Int))]
def n0704Num : Poly := n0704NumPart0

def n0704NF : NF := ⟨n0704Num, (1974375 : Int)⟩

def n0704QPart0 : Poly := []
def n0704Q : Poly := n0704QPart0

def n0704Row : Row := ⟨n0704NF, .mul 4 703, (1 : Int), n0704Q⟩

def n0705NumPart0 : Poly := [(pm0, (-466539128704633856 : Int)), (pm1, (-16359838252978726224 : Int))]
def n0705Num : Poly := n0705NumPart0

def n0705NF : NF := ⟨n0705Num, (148078125 : Int)⟩

def n0705QPart0 : Poly := []
def n0705Q : Poly := n0705QPart0

def n0705Row : Row := ⟨n0705NF, .add 698 704, (1 : Int), n0705Q⟩

def n0706NumPart0 : Poly := [(pm0, (486000 : Int))]
def n0706Num : Poly := n0706NumPart0

def n0706NF : NF := ⟨n0706Num, (1 : Int)⟩

def n0706QPart0 : Poly := []
def n0706Q : Poly := n0706QPart0

def n0706Row : Row := ⟨n0706NF, .lit (486000 : Int) (1 : Int), (1 : Int), n0706Q⟩

def n0707NumPart0 : Poly := [(pm1, (486000 : Int))]
def n0707Num : Poly := n0707NumPart0

def n0707NF : NF := ⟨n0707Num, (1 : Int)⟩

def n0707QPart0 : Poly := []
def n0707Q : Poly := n0707QPart0

def n0707Row : Row := ⟨n0707NF, .mul 0 706, (1 : Int), n0707Q⟩

def n0708NumPart0 : Poly := [(pm0, (-6717019286373376 : Int)), (pm1, (-235541549049320304 : Int))]
def n0708Num : Poly := n0708NumPart0

def n0708NF : NF := ⟨n0708Num, (3553875 : Int)⟩

def n0708QPart0 : Poly := [(pm0, (-83923055565328763550000 : Int))]
def n0708Q : Poly := n0708QPart0

def n0708Row : Row := ⟨n0708NF, .mul 169 707, (1 : Int), n0708Q⟩

def n0709NumPart0 : Poly := [(pm0, (-158964801040023356416 : Int)), (pm1, (-5574320079331662724464 : Int))]
def n0709Num : Poly := n0709NumPart0

def n0709NF : NF := ⟨n0709Num, (2221171875 : Int)⟩

def n0709QPart0 : Poly := [(pm0, (-895216140865684667279250000 : Int))]
def n0709Q : Poly := n0709QPart0

def n0709Row : Row := ⟨n0709NF, .mul 10 708, (1 : Int), n0709Q⟩

def n0710NumPart0 : Poly := [(pm0, (-165962887970592864256 : Int)), (pm1, (-5819717653126343617824 : Int))]
def n0710Num : Poly := n0710NumPart0

def n0710NF : NF := ⟨n0710Num, (2221171875 : Int)⟩

def n0710QPart0 : Poly := []
def n0710Q : Poly := n0710QPart0

def n0710Row : Row := ⟨n0710NF, .add 705 709, (1 : Int), n0710Q⟩

def n0711NumPart0 : Poly := [(pm0, (738720 : Int))]
def n0711Num : Poly := n0711NumPart0

def n0711NF : NF := ⟨n0711Num, (1 : Int)⟩

def n0711QPart0 : Poly := []
def n0711Q : Poly := n0711QPart0

def n0711Row : Row := ⟨n0711NF, .lit (738720 : Int) (1 : Int), (1 : Int), n0711Q⟩

def n0712NumPart0 : Poly := [(pm1, (738720 : Int))]
def n0712Num : Poly := n0712NumPart0

def n0712NF : NF := ⟨n0712Num, (1 : Int)⟩

def n0712QPart0 : Poly := []
def n0712Q : Poly := n0712QPart0

def n0712Row : Row := ⟨n0712NF, .mul 0 711, (1 : Int), n0712Q⟩

def n0713NumPart0 : Poly := [(pm0, (-255246732882188288 : Int)), (pm1, (-8950578863874171552 : Int))]
def n0713Num : Poly := n0713NumPart0

def n0713NF : NF := ⟨n0713Num, (88846875 : Int)⟩

def n0713QPart0 : Poly := [(pm0, (-3189076111482493014900000 : Int))]
def n0713Q : Poly := n0713QPart0

def n0713Row : Row := ⟨n0713NF, .mul 169 712, (1 : Int), n0713Q⟩

def n0714NumPart0 : Poly := [(pm0, (-39266516934045079552 : Int)), (pm1, (-1376934594066234011808 : Int))]
def n0714Num : Poly := n0714NumPart0

def n0714NF : NF := ⟨n0714Num, (2221171875 : Int)⟩

def n0714QPart0 : Poly := [(pm0, (-441794978609039186449500000 : Int))]
def n0714Q : Poly := n0714QPart0

def n0714Row : Row := ⟨n0714NF, .mul 2 713, (1 : Int), n0714Q⟩

def n0715NumPart0 : Poly := [(pm0, (39266516934045079552 : Int)), (pm1, (1376934594066234011808 : Int))]
def n0715Num : Poly := n0715NumPart0

def n0715NF : NF := ⟨n0715Num, (2221171875 : Int)⟩

def n0715QPart0 : Poly := []
def n0715Q : Poly := n0715QPart0

def n0715Row : Row := ⟨n0715NF, .mul 4 714, (1 : Int), n0715Q⟩

def n0716NumPart0 : Poly := [(pm0, (-42232123678849261568 : Int)), (pm1, (-1480927686353369868672 : Int))]
def n0716Num : Poly := n0716NumPart0

def n0716NF : NF := ⟨n0716Num, (740390625 : Int)⟩

def n0716QPart0 : Poly := []
def n0716Q : Poly := n0716QPart0

def n0716Row : Row := ⟨n0716NF, .add 710 715, (1 : Int), n0716Q⟩

def n0717NumPart0 : Poly := [(pm0, (225504 : Int))]
def n0717Num : Poly := n0717NumPart0

def n0717NF : NF := ⟨n0717Num, (1 : Int)⟩

def n0717QPart0 : Poly := []
def n0717Q : Poly := n0717QPart0

def n0717Row : Row := ⟨n0717NF, .lit (225504 : Int) (1 : Int), (1 : Int), n0717Q⟩

def n0718NumPart0 : Poly := [(pm1, (225504 : Int))]
def n0718Num : Poly := n0718NumPart0

def n0718NF : NF := ⟨n0718Num, (1 : Int)⟩

def n0718QPart0 : Poly := []
def n0718Q : Poly := n0718QPart0

def n0718Row : Row := ⟨n0718NF, .mul 0 717, (1 : Int), n0718Q⟩

def n0719NumPart0 : Poly := [(pm0, (-389587118609655808 : Int)), (pm1, (-13661409844860577632 : Int))]
def n0719Num : Poly := n0719NumPart0

def n0719NF : NF := ⟨n0719Num, (444234375 : Int)⟩

def n0719QPart0 : Poly := [(pm0, (-4867537222789068285900000 : Int))]
def n0719Q : Poly := n0719QPart0

def n0719Row : Row := ⟨n0719NF, .mul 169 718, (1 : Int), n0719Q⟩

def n0720NumPart0 : Poly := [(pm0, (-128644306629596063744 : Int)), (pm1, (-4511090108284412494176 : Int))]
def n0720Num : Poly := n0720NumPart0

def n0720NF : NF := ⟨n0720Num, (2221171875 : Int)⟩

def n0720QPart0 : Poly := []
def n0720Q : Poly := n0720QPart0

def n0720Row : Row := ⟨n0720NF, .add 716 719, (1 : Int), n0720Q⟩

def n0721NumPart0 : Poly := [(pm0, (50400 : Int))]
def n0721Num : Poly := n0721NumPart0

def n0721NF : NF := ⟨n0721Num, (1 : Int)⟩

def n0721QPart0 : Poly := []
def n0721Q : Poly := n0721QPart0

def n0721Row : Row := ⟨n0721NF, .lit (50400 : Int) (1 : Int), (1 : Int), n0721Q⟩

def n0722NumPart0 : Poly := [(pm1, (50400 : Int))]
def n0722Num : Poly := n0722NumPart0

def n0722NF : NF := ⟨n0722Num, (1 : Int)⟩

def n0722QPart0 : Poly := []
def n0722Q : Poly := n0722QPart0

def n0722Row : Row := ⟨n0722NF, .mul 0 721, (1 : Int), n0722Q⟩

def n0723NumPart0 : Poly := [(pm0, (2705297975296 : Int)), (pm1, (94865006373984 : Int))]
def n0723Num : Poly := n0723NumPart0

def n0723NF : NF := ⟨n0723Num, (710775 : Int)⟩

def n0723QPart0 : Poly := [(pm0, (50074431468516000 : Int))]
def n0723Q : Poly := n0723QPart0

def n0723Row : Row := ⟨n0723NF, .mul 40 722, (1 : Int), n0723Q⟩

def n0724NumPart0 : Poly := [(pm0, (4924885431273472 : Int)), (pm1, (172697902732843488 : Int))]
def n0724Num : Poly := n0724NumPart0

def n0724NF : NF := ⟨n0724Num, (34171875 : Int)⟩

def n0724QPart0 : Poly := [(pm0, (5546934794573795700000 : Int))]
def n0724Q : Poly := n0724QPart0

def n0724Row : Row := ⟨n0724NF, .mul 10 723, (1 : Int), n0724Q⟩

def n0725NumPart0 : Poly := [(pm0, (-42774729692187762688 : Int)), (pm1, (-1499954914868925889152 : Int))]
def n0725Num : Poly := n0725NumPart0

def n0725NF : NF := ⟨n0725Num, (740390625 : Int)⟩

def n0725QPart0 : Poly := []
def n0725Q : Poly := n0725QPart0

def n0725Row : Row := ⟨n0725NF, .add 720 724, (1 : Int), n0725Q⟩

def n0726NumPart0 : Poly := [(pm0, (21888 : Int))]
def n0726Num : Poly := n0726NumPart0

def n0726NF : NF := ⟨n0726Num, (1 : Int)⟩

def n0726QPart0 : Poly := []
def n0726Q : Poly := n0726QPart0

def n0726Row : Row := ⟨n0726NF, .lit (21888 : Int) (1 : Int), (1 : Int), n0726Q⟩

def n0727NumPart0 : Poly := [(pm1, (21888 : Int))]
def n0727Num : Poly := n0727NumPart0

def n0727NF : NF := ⟨n0727Num, (1 : Int)⟩

def n0727QPart0 : Poly := []
def n0727Q : Poly := n0727QPart0

def n0727Row : Row := ⟨n0727NF, .mul 0 726, (1 : Int), n0727Q⟩

def n0728NumPart0 : Poly := [(pm0, (29371806588928 : Int)), (pm1, (1029962926346112 : Int))]
def n0728Num : Poly := n0728NumPart0

def n0728NF : NF := ⟨n0728Num, (17769375 : Int)⟩

def n0728QPart0 : Poly := [(pm0, (543665255943888000 : Int))]
def n0728Q : Poly := n0728QPart0

def n0728Row : Row := ⟨n0728NF, .mul 40 727, (1 : Int), n0728Q⟩

def n0729NumPart0 : Poly := [(pm0, (4518485039194112 : Int)), (pm1, (158446912256178048 : Int))]
def n0729Num : Poly := n0729NumPart0

def n0729NF : NF := ⟨n0729Num, (444234375 : Int)⟩

def n0729QPart0 : Poly := [(pm0, (10167665263523024400000 : Int))]
def n0729Q : Poly := n0729QPart0

def n0729Row : Row := ⟨n0729NF, .mul 2 728, (1 : Int), n0729Q⟩

def n0730NumPart0 : Poly := [(pm0, (-4518485039194112 : Int)), (pm1, (-158446912256178048 : Int))]
def n0730Num : Poly := n0730NumPart0

def n0730NF : NF := ⟨n0730Num, (444234375 : Int)⟩

def n0730QPart0 : Poly := []
def n0730Q : Poly := n0730QPart0

def n0730Row : Row := ⟨n0730NF, .mul 4 729, (1 : Int), n0730Q⟩

def n0731NumPart0 : Poly := [(pm0, (-128346781501759258624 : Int)), (pm1, (-4500656979168058557696 : Int))]
def n0731Num : Poly := n0731NumPart0

def n0731NF : NF := ⟨n0731Num, (2221171875 : Int)⟩

def n0731QPart0 : Poly := []
def n0731Q : Poly := n0731QPart0

def n0731Row : Row := ⟨n0731NF, .add 725 730, (1 : Int), n0731Q⟩

def n0732NumPart0 : Poly := [(pm0, (1152 : Int))]
def n0732Num : Poly := n0732NumPart0

def n0732NF : NF := ⟨n0732Num, (1 : Int)⟩

def n0732QPart0 : Poly := []
def n0732Q : Poly := n0732QPart0

def n0732Row : Row := ⟨n0732NF, .lit (1152 : Int) (1 : Int), (1 : Int), n0732Q⟩

def n0733NumPart0 : Poly := [(pm1, (1152 : Int))]
def n0733Num : Poly := n0733NumPart0

def n0733NF : NF := ⟨n0733Num, (1 : Int)⟩

def n0733QPart0 : Poly := []
def n0733Q : Poly := n0733QPart0

def n0733Row : Row := ⟨n0733NF, .mul 0 732, (1 : Int), n0733Q⟩

def n0734NumPart0 : Poly := [(pm0, (1545884557312 : Int)), (pm1, (54208575070848 : Int))]
def n0734Num : Poly := n0734NumPart0

def n0734NF : NF := ⟨n0734Num, (17769375 : Int)⟩

def n0734QPart0 : Poly := [(pm0, (28613960839152000 : Int))]
def n0734Q : Poly := n0734QPart0

def n0734Row : Row := ⟨n0734NF, .mul 40 733, (1 : Int), n0734Q⟩

def n0735NumPart0 : Poly := [(pm0, (-128346588266189594624 : Int)), (pm1, (-4500650203096174701696 : Int))]
def n0735Num : Poly := n0735NumPart0

def n0735NF : NF := ⟨n0735Num, (2221171875 : Int)⟩

def n0735QPart0 : Poly := []
def n0735Q : Poly := n0735QPart0

def n0735Row : Row := ⟨n0735NF, .add 731 734, (1 : Int), n0735Q⟩

def n0736NumPart0 : Poly := [(pm0, (-44474368 : Int)), (pm1, (-1559475072 : Int))]
def n0736Num : Poly := n0736NumPart0

def n0736NF : NF := ⟨n0736Num, (8775 : Int)⟩

def n0736QPart0 : Poly := [(pm0, (-135507840 : Int))]
def n0736Q : Poly := n0736QPart0

def n0736Row : Row := ⟨n0736NF, .mul 3 270, (1 : Int), n0736Q⟩

def n0737NumPart0 : Poly := [(pm0, (-1052475301888 : Int)), (pm1, (-36906498605952 : Int))]
def n0737Num : Poly := n0737NumPart0

def n0737NF : NF := ⟨n0737Num, (5484375 : Int)⟩

def n0737QPart0 : Poly := [(pm0, (-14634698878800000 : Int))]
def n0737Q : Poly := n0737QPart0

def n0737Row : Row := ⟨n0737NF, .mul 10 736, (1 : Int), n0737Q⟩

def n0738NumPart0 : Poly := [(pm0, (-128347014518686859264 : Int)), (pm1, (-4500665150228110112256 : Int))]
def n0738Num : Poly := n0738NumPart0

def n0738NF : NF := ⟨n0738Num, (2221171875 : Int)⟩

def n0738QPart0 : Poly := []
def n0738Q : Poly := n0738QPart0

def n0738Row : Row := ⟨n0738NF, .add 735 737, (1 : Int), n0738Q⟩

def n0739NumPart0 : Poly := [(pm0, (21210478144 : Int)), (pm1, (743774681151 : Int))]
def n0739Num : Poly := n0739NumPart0

def n0739NF : NF := ⟨n0739Num, (500000 : Int)⟩

def n0739QPart0 : Poly := [(pm0, (5527009557900000 : Int))]
def n0739Q : Poly := n0739QPart0

def n0739Row : Row := ⟨n0739NF, .mul 1 356, (1 : Int), n0739Q⟩

def n0740NumPart0 : Poly := [(pm0, (678735300608 : Int)), (pm1, (23800789796832 : Int))]
def n0740Num : Poly := n0740NumPart0

def n0740NF : NF := ⟨n0740Num, (15625 : Int)⟩

def n0740QPart0 : Poly := []
def n0740Q : Poly := n0740QPart0

def n0740Row : Row := ⟨n0740NF, .mul 355 739, (1 : Int), n0740Q⟩

def n0741NumPart0 : Poly := [(pm0, (-128250528902028929024 : Int)), (pm1, (-4497281748954541459296 : Int))]
def n0741Num : Poly := n0741NumPart0

def n0741NF : NF := ⟨n0741Num, (2221171875 : Int)⟩

def n0741QPart0 : Poly := []
def n0741Q : Poly := n0741QPart0

def n0741Row : Row := ⟨n0741NF, .add 738 740, (1 : Int), n0741Q⟩

def n0742NumPart0 : Poly := [(pm0, (75655502848 : Int)), (pm1, (2652964587792 : Int))]
def n0742Num : Poly := n0742NumPart0

def n0742NF : NF := ⟨n0742Num, (40625 : Int)⟩

def n0742QPart0 : Poly := []
def n0742Q : Poly := n0742QPart0

def n0742Row : Row := ⟨n0742NF, .mul 356 360, (1 : Int), n0742Q⟩

def n0743NumPart0 : Poly := [(pm0, (-75655502848 : Int)), (pm1, (-2652964587792 : Int))]
def n0743Num : Poly := n0743NumPart0

def n0743NF : NF := ⟨n0743Num, (40625 : Int)⟩

def n0743QPart0 : Poly := []
def n0743Q : Poly := n0743QPart0

def n0743Row : Row := ⟨n0743NF, .mul 4 742, (1 : Int), n0743Q⟩

def n0744NumPart0 : Poly := [(pm0, (-128254665366647143424 : Int)), (pm1, (-4497426799793378986896 : Int))]
def n0744Num : Poly := n0744NumPart0

def n0744NF : NF := ⟨n0744Num, (2221171875 : Int)⟩

def n0744QPart0 : Poly := []
def n0744Q : Poly := n0744QPart0

def n0744Row : Row := ⟨n0744NF, .add 741 743, (1 : Int), n0744Q⟩

def n0745NumPart0 : Poly := [(pm0, (3072 : Int))]
def n0745Num : Poly := n0745NumPart0

def n0745NF : NF := ⟨n0745Num, (1 : Int)⟩

def n0745QPart0 : Poly := []
def n0745Q : Poly := n0745QPart0

def n0745Row : Row := ⟨n0745NF, .lit (3072 : Int) (1 : Int), (1 : Int), n0745Q⟩

def n0746NumPart0 : Poly := [(pm0, (7784282112 : Int)), (pm1, (272966550048 : Int))]
def n0746Num : Poly := n0746NumPart0

def n0746NF : NF := ⟨n0746Num, (8125 : Int)⟩

def n0746QPart0 : Poly := []
def n0746Q : Poly := n0746QPart0

def n0746Row : Row := ⟨n0746NF, .mul 215 745, (1 : Int), n0746Q⟩

def n0747NumPart0 : Poly := [(pm0, (-10021765986304 : Int)), (pm1, (-351427051792416 : Int))]
def n0747Num : Poly := n0747NumPart0

def n0747NF : NF := ⟨n0747Num, (203125 : Int)⟩

def n0747QPart0 : Poly := [(pm0, (-247751545817100000 : Int))]
def n0747Q : Poly := n0747QPart0

def n0747Row : Row := ⟨n0747NF, .mul 3 746, (1 : Int), n0747Q⟩

def n0748NumPart0 : Poly := [(pm0, (-128364253377707377664 : Int)), (pm1, (-4501269654604729055856 : Int))]
def n0748Num : Poly := n0748NumPart0

def n0748NF : NF := ⟨n0748Num, (2221171875 : Int)⟩

def n0748QPart0 : Poly := []
def n0748Q : Poly := n0748QPart0

def n0748Row : Row := ⟨n0748NF, .add 744 747, (1 : Int), n0748Q⟩

def n0749NumPart0 : Poly := [(pm0, (162172544 : Int)), (pm1, (5686803126 : Int))]
def n0749Num : Poly := n0749NumPart0

def n0749NF : NF := ⟨n0749Num, (8125 : Int)⟩

def n0749QPart0 : Poly := []
def n0749Q : Poly := n0749QPart0

def n0749Row : Row := ⟨n0749NF, .mul 215 370, (1 : Int), n0749Q⟩

def n0750NumPart0 : Poly := [(pm0, (-128364209043788161664 : Int)), (pm1, (-4501268099974924485606 : Int))]
def n0750Num : Poly := n0750NumPart0

def n0750NF : NF := ⟨n0750Num, (2221171875 : Int)⟩

def n0750QPart0 : Poly := []
def n0750Q : Poly := n0750QPart0

def n0750Row : Row := ⟨n0750NF, .add 748 749, (1 : Int), n0750Q⟩

def n0751NumPart0 : Poly := [(pm0, (96768 : Int))]
def n0751Num : Poly := n0751NumPart0

def n0751NF : NF := ⟨n0751Num, (1 : Int)⟩

def n0751QPart0 : Poly := []
def n0751Q : Poly := n0751QPart0

def n0751Row : Row := ⟨n0751NF, .lit (96768 : Int) (1 : Int), (1 : Int), n0751Q⟩

def n0752NumPart0 : Poly := [(pm0, (4204956672 : Int)), (pm1, (147450654288 : Int))]
def n0752Num : Poly := n0752NumPart0

def n0752NF : NF := ⟨n0752Num, (1625 : Int)⟩

def n0752QPart0 : Poly := []
def n0752Q : Poly := n0752QPart0

def n0752Row : Row := ⟨n0752NF, .mul 214 751, (1 : Int), n0752Q⟩

def n0753NumPart0 : Poly := [(pm0, (188178958790050816 : Int)), (pm1, (6598754828919422064 : Int))]
def n0753Num : Poly := n0753NumPart0

def n0753NF : NF := ⟨n0753Num, (27421875 : Int)⟩

def n0753QPart0 : Poly := [(pm0, (5651935506023035524750000 : Int))]
def n0753Q : Poly := n0753QPart0

def n0753Row : Row := ⟨n0753NF, .mul 40 752, (1 : Int), n0753Q⟩

def n0754NumPart0 : Poly := [(pm0, (-188178958790050816 : Int)), (pm1, (-6598754828919422064 : Int))]
def n0754Num : Poly := n0754NumPart0

def n0754NF : NF := ⟨n0754Num, (27421875 : Int)⟩

def n0754QPart0 : Poly := []
def n0754Q : Poly := n0754QPart0

def n0754Row : Row := ⟨n0754NF, .mul 4 753, (1 : Int), n0754Q⟩

def n0755NumPart0 : Poly := [(pm0, (-28721340941156455552 : Int)), (pm1, (-1007153448223479534558 : Int))]
def n0755Num : Poly := n0755NumPart0

def n0755NF : NF := ⟨n0755Num, (444234375 : Int)⟩

def n0755QPart0 : Poly := []
def n0755Q : Poly := n0755QPart0

def n0755Row : Row := ⟨n0755NF, .add 750 754, (1 : Int), n0755Q⟩

def n0756NumPart0 : Poly := [(pm0, (2816 : Int))]
def n0756Num : Poly := n0756NumPart0

def n0756NF : NF := ⟨n0756Num, (1 : Int)⟩

def n0756QPart0 : Poly := []
def n0756Q : Poly := n0756QPart0

def n0756Row : Row := ⟨n0756NF, .lit (2816 : Int) (1 : Int), (1 : Int), n0756Q⟩

def n0757NumPart0 : Poly := [(pm0, (122366464 : Int)), (pm1, (4290892056 : Int))]
def n0757Num : Poly := n0757NumPart0

def n0757NF : NF := ⟨n0757Num, (1625 : Int)⟩

def n0757QPart0 : Poly := []
def n0757Q : Poly := n0757QPart0

def n0757Row : Row := ⟨n0757NF, .mul 214 756, (1 : Int), n0757Q⟩

def n0758NumPart0 : Poly := [(pm0, (-157536946688 : Int)), (pm1, (-5524250400152 : Int))]
def n0758Num : Poly := n0758NumPart0

def n0758NF : NF := ⟨n0758Num, (40625 : Int)⟩

def n0758QPart0 : Poly := [(pm0, (-778905063365000 : Int))]
def n0758Q : Poly := n0758QPart0

def n0758Row : Row := ⟨n0758NF, .mul 3 757, (1 : Int), n0758Q⟩

def n0759NumPart0 : Poly := [(pm0, (157536946688 : Int)), (pm1, (5524250400152 : Int))]
def n0759Num : Poly := n0759NumPart0

def n0759NF : NF := ⟨n0759Num, (40625 : Int)⟩

def n0759QPart0 : Poly := []
def n0759Q : Poly := n0759QPart0

def n0759Row : Row := ⟨n0759NF, .mul 4 758, (1 : Int), n0759Q⟩

def n0760NumPart0 : Poly := [(pm0, (-28719618274644422272 : Int)), (pm1, (-1007093040545353872438 : Int))]
def n0760Num : Poly := n0760NumPart0

def n0760NF : NF := ⟨n0760Num, (444234375 : Int)⟩

def n0760QPart0 : Poly := []
def n0760Q : Poly := n0760QPart0

def n0760Row : Row := ⟨n0760NF, .add 755 759, (1 : Int), n0760Q⟩

def n0761NumPart0 : Poly := [(pm0, (26496 : Int))]
def n0761Num : Poly := n0761NumPart0

def n0761NF : NF := ⟨n0761Num, (1 : Int)⟩

def n0761QPart0 : Poly := []
def n0761Q : Poly := n0761QPart0

def n0761Row : Row := ⟨n0761NF, .lit (26496 : Int) (1 : Int), (1 : Int), n0761Q⟩

def n0762NumPart0 : Poly := [(pm0, (19766016 : Int)), (pm1, (692342964 : Int))]
def n0762Num : Poly := n0762NumPart0

def n0762NF : NF := ⟨n0762Num, (325 : Int)⟩

def n0762QPart0 : Poly := []
def n0762Q : Poly := n0762QPart0

def n0762Row : Row := ⟨n0762NF, .mul 77 761, (1 : Int), n0762Q⟩

def n0763NumPart0 : Poly := [(pm0, (2650742818482944 : Int)), (pm1, (92951954278543476 : Int))]
def n0763Num : Poly := n0763NumPart0

def n0763NF : NF := ⟨n0763Num, (16453125 : Int)⟩

def n0763QPart0 : Poly := [(pm0, (15922931503310203612500 : Int))]
def n0763Q : Poly := n0763QPart0

def n0763Row : Row := ⟨n0763NF, .mul 40 762, (1 : Int), n0763Q⟩

def n0764NumPart0 : Poly := [(pm0, (-28648048218545382784 : Int)), (pm1, (-1004583337779833198586 : Int))]
def n0764Num : Poly := n0764NumPart0

def n0764NF : NF := ⟨n0764Num, (444234375 : Int)⟩

def n0764QPart0 : Poly := []
def n0764Q : Poly := n0764QPart0

def n0764Row : Row := ⟨n0764NF, .add 760 763, (1 : Int), n0764Q⟩

def n0765NumPart0 : Poly := [(pm0, (381952 : Int)), (pm1, (13378608 : Int))]
def n0765Num : Poly := n0765NumPart0

def n0765NF : NF := ⟨n0765Num, (325 : Int)⟩

def n0765QPart0 : Poly := []
def n0765Q : Poly := n0765QPart0

def n0765Row : Row := ⟨n0765NF, .mul 77 360, (1 : Int), n0765Q⟩

def n0766NumPart0 : Poly := [(pm0, (-1473559552 : Int)), (pm1, (-51672401808 : Int))]
def n0766Num : Poly := n0766NumPart0

def n0766NF : NF := ⟨n0766Num, (24375 : Int)⟩

def n0766QPart0 : Poly := [(pm0, (-1457132742000 : Int))]
def n0766Q : Poly := n0766QPart0

def n0766Row : Row := ⟨n0766NF, .mul 3 765, (1 : Int), n0766Q⟩

def n0767NumPart0 : Poly := [(pm0, (-28648075074168217984 : Int)), (pm1, (-1004584279509356149386 : Int))]
def n0767Num : Poly := n0767NumPart0

def n0767NF : NF := ⟨n0767Num, (444234375 : Int)⟩

def n0767QPart0 : Poly := []
def n0767Q : Poly := n0767QPart0

def n0767Row : Row := ⟨n0767NF, .add 764 766, (1 : Int), n0767Q⟩

end N6.BranchEval.B2.ProgramData
