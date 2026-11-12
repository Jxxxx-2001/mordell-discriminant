import N6.Univariate.Core
namespace N6.Univariate.Branch5
def p : List Rat := [(41028905953125 : Rat), (3163070401875 : Rat), (278789519925 : Rat), (8387759547 : Rat), (-266663097 : Rat), (1775601 : Rat), (-2529 : Rat), (1 : Rat)]
def v : List Rat := [((96011811030692012969141145544163328 : Rat) / 597653255522251129150390625), ((-280547265418177091499161588770799616 : Rat) / 14941331388056278228759765625), ((-413396943908476405247633987510206464 : Rat) / 373533284701406955718994140625), ((222688702142133214277481136165748736 : Rat) / 9338332117535173892974853515625), ((-1284598550522630153670304692436992 : Rat) / 9338332117535173892974853515625), ((1820950766309381872712587149312 : Rat) / 9338332117535173892974853515625), ((-727253268146689416404926464 : Rat) / 9338332117535173892974853515625)]
def chunk000 : Cover := (.split ((225 : Rat) / 2) (.split ((225 : Rat) / 4) (.split ((225 : Rat) / 8) .leaf .leaf) (.split ((675 : Rat) / 8) (.split ((1125 : Rat) / 16) .leaf (.split ((2475 : Rat) / 32) .leaf .leaf)) (.split ((1575 : Rat) / 16) (.split ((2925 : Rat) / 32) .leaf .leaf) (.split ((3375 : Rat) / 32) .leaf .leaf)))) (.split ((675 : Rat) / 4) (.split ((1125 : Rat) / 8) (.split ((2025 : Rat) / 16) (.split ((3825 : Rat) / 32) .leaf (.split ((7875 : Rat) / 64) .leaf .leaf)) (.split ((4275 : Rat) / 32) (.split ((8325 : Rat) / 64) .leaf .leaf) .leaf)) (.split ((2475 : Rat) / 16) (.split ((4725 : Rat) / 32) .leaf .leaf) .leaf)) (.split ((1575 : Rat) / 8) .leaf .leaf)))
def box000 : Bounds := ⟨(0 : Rat), (225 : Rat)⟩
def tree : Cover := chunk000
end N6.Univariate.Branch5
