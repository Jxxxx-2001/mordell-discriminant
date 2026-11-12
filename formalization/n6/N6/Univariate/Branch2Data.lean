import N6.Univariate.Core
namespace N6.Univariate.Branch2
def p : List Rat := [(2025 : Rat), (-1386 : Rat), (1 : Rat)]
def v : List Rat := [((37144335666598255871347654656 : Rat) / 37252902984619140625), ((512752752212267763559053656064 : Rat) / 931322574615478515625)]
def chunk000 : Cover := (.split ((225 : Rat) / 2) (.split ((225 : Rat) / 4) (.split ((225 : Rat) / 8) (.split ((225 : Rat) / 16) (.split ((225 : Rat) / 32) (.split ((225 : Rat) / 64) (.split ((225 : Rat) / 128) .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)
def box000 : Bounds := ⟨(0 : Rat), (225 : Rat)⟩
def tree : Cover := chunk000
end N6.Univariate.Branch2
