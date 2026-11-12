import Eight.PackedRoots.B29.C18

namespace MordellEight.NarrowPositive
open FixedTensor RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Row29Leaf18
def box : ClosedBox 3 := ⟨![(6756869/4194304),(6756869/4194304),(2895801/4194304)],![(965267/524288),(965267/524288),(965267/1048576)]⟩
def a : ℚ := (2254159/1048576)
def lo : ℚ := (231311000747721680216277/302231454903657293676544)
def hi : ℚ := (462622001495443360432555/604462909807314587353088)
theorem logarithm_checked : logCheck a lo hi 64=true := by decide +kernel
theorem positive : (0:ℝ)<(a:ℝ) := by norm_num [a]
theorem logarithm : Real.log (a:ℝ)≤(hi:ℝ) :=
  (logCheck_sound a lo hi 64 logarithm_checked).2
theorem parameters_checked : IntegerLeaf.parameters box a hi 1267650600228229401496703205376 2254159 (-1694408478165149853154289284490) (-291734049780488564895276597248) (-291734049780488564895276597248) (583468099560977129790553194496)=true := by decide +kernel
theorem gap_checked : IntegerCube.nonneg (IntegerLeaf.gap S2R0R1R2L0R1R2R0R1R2R.controls 2254159 (-1694408478165149853154289284490) (-291734049780488564895276597248) (-291734049780488564895276597248) (583468099560977129790553194496))=true := by decide +kernel
theorem bound : BoxMajorant box :=
  IntegerLeaf.majorant S2R0R1R2L0R1R2R0R1R2R.widths S2R0R1R2L0R1R2R0R1R2R.valid a hi 1267650600228229401496703205376 2254159 (-1694408478165149853154289284490) (-291734049780488564895276597248) (-291734049780488564895276597248) (583468099560977129790553194496)
    parameters_checked gap_checked positive logarithm
end Row29Leaf18

end MordellEight.NarrowPositive
