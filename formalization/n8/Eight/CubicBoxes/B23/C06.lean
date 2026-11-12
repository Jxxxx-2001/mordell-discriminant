import Eight.CubicBoxes.B23.C05
namespace MordellEight.CubicBoxes.B23
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Leaf4
def box : ClosedBox 3 := ⟨![(2895801/4194304),(6756869/4194304),(4826335/4194304)],![(965267/1048576),(965267/524288),(2895801/2097152)]⟩
def a : ℚ := (1/2)
def lo : ℚ := (-837963543211955903118923/1208925819614629174706176)
def hi : ℚ := (-104745437635737052434027/151115727451828646838272)
def terms : List CubicLeaf.Term := [⟨(9162982511138149719300616),0,0,0⟩,⟨(10015893737886036239843328),0,0,1⟩,⟨(4610067224830646773874688),0,0,2⟩,⟨(943066440139474639781888),0,0,3⟩,⟨(-5007946868943018119921664),0,1,0⟩,⟨(-4610067224830646773874688),0,1,1⟩,⟨(-1414599660209211959672832),0,1,2⟩,⟨(1152516806207661693468672),0,2,0⟩,⟨(707299830104605979836416),0,2,1⟩,⟨(-117883305017434329972736),0,3,0⟩,⟨(-5007946868943018119921664),1,0,0⟩,⟨(-4610067224830646773874688),1,0,1⟩,⟨(-1414599660209211959672832),1,0,2⟩,⟨(2305033612415323386937344),1,1,0⟩,⟨(1414599660209211959672832),1,1,1⟩,⟨(-353649915052302989918208),1,2,0⟩,⟨(1152516806207661693468672),2,0,0⟩,⟨(707299830104605979836416),2,0,1⟩,⟨(-353649915052302989918208),2,1,0⟩,⟨(-117883305017434329972736),3,0,0⟩]
theorem log_checked : logCheck a lo hi 8=true := by decide +kernel
theorem log_upper : Real.log (a:ℝ)≤(hi:ℝ) := (logCheck_sound a lo hi 8 log_checked).2
theorem ident (u v t : ℝ) : CubicLeaf.value u v t terms=
    -((3:Int):ℝ)*2^80*CubicLeaf.upper hi (CubicLeaf.dist box u v t/a-1) := by
  norm_num [terms,CubicLeaf.value,CubicLeaf.dist,CubicLeaf.upper,box,a,hi,Matrix.cons_val_two] <;> ring
theorem checked : IntegerCube.nonneg (CubicLeaf.gap S2R0L1R2R0R1R2L0R1R2R.controls 3 terms)=true := by decide +kernel
theorem bound : BoxMajorant box :=
  CubicLeaf.majorant S2R0L1R2R0R1R2L0R1R2R.widths S2R0L1R2R0R1R2L0R1R2R.valid a hi 3 terms
    (by norm_num) (by norm_num [a]) log_upper (fun u v t => by simpa [mul_assoc] using ident u v t) checked
end Leaf4

end MordellEight.CubicBoxes.B23
