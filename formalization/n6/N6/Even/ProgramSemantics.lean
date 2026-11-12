import N6.Even.ProgramGround
import N6.Even.RawBindings
import N6.BranchEval.ProgramBinding

set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
namespace N6.Even.ProgramData
open N6.SparseCheck N6.BranchEval.Program

variable {K : Type*} [Field K] [CharZero K]

def actualD (c e : K) : K := (((((((((((((((1024 : K)*(c^6))*e)-(((512 : K)*(c^5))*e))-(((9216 : K)*(c^4))*(e^2)))+(((64 : K)*(c^4))*e))+(((13824 : K)*(c^3))*(e^3)))+(((4352 : K)*(c^3))*(e^2)))+(((17280 : K)*(c^2))*(e^3)))-(((512 : K)*(c^2))*(e^2)))-(((62208 : K)*c)*(e^4)))-(((9216 : K)*c)*(e^3)))+((46656 : K)*(e^5)))+((13824 : K)*(e^4)))+((1024 : K)*(e^3)))

def actualR4 (c e : K) : K := ((((((((((((((((1024 : K)*(c^7))-((512 : K)*(c^6)))+(((3072 : K)*(c^5))*e))+((64 : K)*(c^5)))-(((96768 : K)*(c^4))*(e^2)))-(((2816 : K)*(c^4))*e))+(((26496 : K)*(c^3))*(e^2)))+(((512 : K)*(c^3))*e))+(((518400 : K)*(c^2))*(e^3)))+(((12288 : K)*(c^2))*(e^2)))-(((699840 : K)*c)*(e^4)))-(((290304 : K)*c)*(e^3)))-(((3072 : K)*c)*(e^2)))+((248832 : K)*(e^4)))+((36864 : K)*(e^3)))

def actualR02 (c e : K) : K := ((((((((((((((((21504 : K)*(c^6))+(((2322432 : K)*(c^5))*e))-((11776 : K)*(c^5)))-(((1382400 : K)*(c^4))*e))+((1600 : K)*(c^4)))-(((13561344 : K)*(c^3))*(e^2)))+(((294144 : K)*(c^3))*e))+(((18662400 : K)*(c^2))*(e^3)))+(((6708096 : K)*(c^2))*(e^2)))-(((23040 : K)*(c^2))*e))+(((4665600 : K)*c)*(e^3)))-(((1188864 : K)*c)*(e^2)))-((17496000 : K)*(e^4)))-((1700352 : K)*(e^3)))+((82944 : K)*(e^2)))

def pointC (c : K) : Fin 5 → K := fun i => if i.val=4 then c else 0
noncomputable def C (x : Fin 5 → K) : K := meaning x input0NF
noncomputable def E (x : Fin 5 → K) : K := meaning x input1NF
noncomputable def Di (x : Fin 5 → K) : K := meaning x input2NF
noncomputable def Ri (x : Fin 5 → K) : K := meaning x input3NF
noncomputable def R2i (x : Fin 5 → K) : K := meaning x input4NF
noncomputable def Ay (x : Fin 5 → K) : K := meaning x input5NF
noncomputable def Vi (x : Fin 5 → K) : K := meaning x input6NF
noncomputable def A (c : K) : K := Ay (pointC c)
noncomputable def V (c : K) : K := Vi (pointC c)
theorem checked_program : Checked program := by
  intro i hi
  change i < 196 at hi
  simpa only [Nat.zero_add] using checked_slot all_checked hi

theorem program_law (x : Fin 5 → K) (hf : value x program.factor=0) (i : Nat) (hi : i<program.size) :
    nodeValue x program i = opValue x program (program.row i).op :=
  checkAt_sound x program i hf (checked_program i hi)

theorem literal_field (x : Fin 5 → K) (z d : Int) : meaning x (litNF z d) = (z : K)/(d : K) := by
  simp only [literal_value, map_inv₀, map_intCast, div_eq_mul_inv]
  ring

theorem atom_C (x : Fin 5 → K) (hf : value x program.factor=0) : nodeValue x program 0 = C x := by
  have h := program_law x hf 0 (by decide)
  change nodeValue x program 0 = C x at h
  exact h

theorem atom_E (x : Fin 5 → K) (hf : value x program.factor=0) : nodeValue x program 1 = E x := by
  have h := program_law x hf 1 (by decide)
  change nodeValue x program 1 = E x at h
  exact h

theorem atom_Di (x : Fin 5 → K) (hf : value x program.factor=0) : nodeValue x program 177 = Di x := by
  have h := program_law x hf 177 (by decide)
  change nodeValue x program 177 = Di x at h
  exact h

theorem atom_Ri (x : Fin 5 → K) (hf : value x program.factor=0) : nodeValue x program 178 = Ri x := by
  have h := program_law x hf 178 (by decide)
  change nodeValue x program 178 = Ri x at h
  exact h

theorem atom_R2i (x : Fin 5 → K) (hf : value x program.factor=0) : nodeValue x program 179 = R2i x := by
  have h := program_law x hf 179 (by decide)
  change nodeValue x program 179 = R2i x at h
  exact h

theorem atom_Ay (x : Fin 5 → K) (hf : value x program.factor=0) : nodeValue x program 180 = Ay x := by
  have h := program_law x hf 180 (by decide)
  change nodeValue x program 180 = Ay x at h
  exact h

theorem atom_Vi (x : Fin 5 → K) (hf : value x program.factor=0) : nodeValue x program 195 = Vi x := by
  have h := program_law x hf 195 (by decide)
  change nodeValue x program 195 = Vi x at h
  exact h

theorem actualD_expr_value (x : Fin 5 → K) (hf : value x program.factor=0) :
    exprValue x program actualDExpr = actualD (C x) (E x) := by
  simp only [actualDExpr, e060, e059, e058, e057, e056, e055, e054, e053, e052, e051, e050, e049, e048, e047, e046, e045, e044, e043, e042, e041, e040, e039, e038, e037, e036, e035, e034, e033, e032, e031, e030, e029, e028, e027, e026, e025, e024, e023, e022, e021, e020, e019, e018, e017, e016, e015, e014, e013, e012, e011, e010, e009, e008, e007, e006, e005, e004, e003, e002, e001, e000, exprValue, literal_field, atom_C x hf, atom_E x hf]
  norm_num [actualD] <;> ring

theorem node_actualD (x : Fin 5 → K) (hf : value x program.factor=0) :
    nodeValue x program 60 = actualD (C x) (E x) := by
  have h := matchesExpr_sound x program (program_law x hf) actualDExpr 60 actualD_binding
  exact h.trans (actualD_expr_value x hf)

theorem actualR4_expr_value (x : Fin 5 → K) (hf : value x program.factor=0) :
    exprValue x program actualR4Expr = actualR4 (C x) (E x) := by
  simp only [actualR4Expr, e116, e115, e114, e113, e112, e111, e110, e109, e108, e107, e106, e105, e104, e103, e102, e101, e100, e099, e098, e097, e096, e095, e094, e093, e092, e091, e090, e089, e088, e087, e086, e085, e084, e083, e082, e081, e080, e079, e078, e077, e076, e075, e074, e073, e072, e071, e070, e069, e068, e067, e066, e065, e064, e063, e062, e061, e045, e028, e022, e018, e013, e010, e009, e008, e005, e004, e003, e002, e001, e000, exprValue, literal_field, atom_C x hf, atom_E x hf]
  norm_num [actualR4] <;> ring

theorem node_actualR4 (x : Fin 5 → K) (hf : value x program.factor=0) :
    nodeValue x program 116 = actualR4 (C x) (E x) := by
  have h := matchesExpr_sound x program (program_law x hf) actualR4Expr 116 actualR4_binding
  exact h.trans (actualR4_expr_value x hf)

theorem actualR02_expr_value (x : Fin 5 → K) (hf : value x program.factor=0) :
    exprValue x program actualR02Expr = actualR02 (C x) (E x) := by
  simp only [actualR02Expr, e176, e175, e174, e173, e172, e171, e170, e169, e168, e167, e166, e165, e164, e163, e162, e161, e160, e159, e158, e157, e156, e155, e154, e153, e152, e151, e150, e149, e148, e147, e146, e145, e144, e143, e142, e141, e140, e139, e138, e137, e136, e135, e134, e133, e132, e131, e130, e129, e128, e127, e126, e125, e124, e123, e122, e121, e120, e119, e118, e117, e045, e028, e018, e013, e010, e009, e005, e004, e003, e001, e000, exprValue, literal_field, atom_C x hf, atom_E x hf]
  norm_num [actualR02] <;> ring

theorem node_actualR02 (x : Fin 5 → K) (hf : value x program.factor=0) :
    nodeValue x program 176 = actualR02 (C x) (E x) := by
  have h := matchesExpr_sound x program (program_law x hf) actualR02Expr 176 actualR02_binding
  exact h.trans (actualR02_expr_value x hf)

theorem DtimesAy_expr_value (x : Fin 5 → K) (hf : value x program.factor=0) :
    exprValue x program DtimesAyExpr = Di x*Ay x := by
  simp only [DtimesAyExpr, e179, e178, e177, exprValue, literal_field, atom_C x hf, atom_Di x hf, atom_Ay x hf, node_actualD x hf, node_actualR4 x hf, node_actualR02 x hf]
  all_goals (norm_num <;> ring_nf <;> simp)

theorem DtimesR02_expr_value (x : Fin 5 → K) (hf : value x program.factor=0) :
    exprValue x program DtimesR02Expr = actualD (C x) (E x)*actualR02 (C x) (E x) := by
  simp only [DtimesR02Expr, e182, e181, e180, exprValue, literal_field, atom_C x hf, atom_Di x hf, atom_Ay x hf, node_actualD x hf, node_actualR4 x hf, node_actualR02 x hf]
  all_goals (norm_num <;> ring_nf <;> simp)

theorem ctimesR4sq_expr_value (x : Fin 5 → K) (hf : value x program.factor=0) :
    exprValue x program ctimesR4sqExpr = C x*(actualR4 (C x) (E x))^2 := by
  simp only [ctimesR4sqExpr, e185, e184, e183, e000, exprValue, literal_field, atom_C x hf, atom_Di x hf, atom_Ay x hf, node_actualD x hf, node_actualR4 x hf, node_actualR02 x hf]
  all_goals (norm_num <;> ring_nf <;> simp)

theorem objectiveFormula_expr_value (x : Fin 5 → K) (hf : value x program.factor=0) :
    exprValue x program objectiveFormulaExpr = (Ay x)^15*(Di x)^2/(5^30 : K) := by
  simp only [objectiveFormulaExpr, e195, e194, e193, e192, e191, e190, e189, e188, e187, e186, e178, e177, exprValue, literal_field, atom_C x hf, atom_Di x hf, atom_Ay x hf, node_actualD x hf, node_actualR4 x hf, node_actualR02 x hf]
  all_goals (norm_num <;> ring_nf <;> simp)

theorem endpoint0 (x : Fin 5 → K) (hf : value x program.factor=0) : actualD (C x) (E x) = Di x := by
  have hn : nodeValue x program 60 = nodeValue x program 177 := congrArg (meaning x) endpoint0_same_nf
  exact (node_actualD x hf).symm.trans (hn.trans (atom_Di x hf))

theorem endpoint1 (x : Fin 5 → K) (hf : value x program.factor=0) : actualR4 (C x) (E x) = Ri x := by
  have hn : nodeValue x program 116 = nodeValue x program 178 := congrArg (meaning x) endpoint1_same_nf
  exact (node_actualR4 x hf).symm.trans (hn.trans (atom_Ri x hf))

theorem endpoint2 (x : Fin 5 → K) (hf : value x program.factor=0) : actualR02 (C x) (E x) = R2i x := by
  have hn : nodeValue x program 176 = nodeValue x program 179 := congrArg (meaning x) endpoint2_same_nf
  exact (node_actualR02 x hf).symm.trans (hn.trans (atom_R2i x hf))

theorem endpoint3 (x : Fin 5 → K) (hf : value x program.factor=0) : Di x*Ay x = Ri x := by
  have h := matchesExpr_sound x program (program_law x hf) DtimesAyExpr 181 DtimesAy_binding
  have hn : nodeValue x program 181 = nodeValue x program 178 := congrArg (meaning x) endpoint3_same_nf
  rw [DtimesAy_expr_value x hf] at h
  exact h.symm.trans (hn.trans (atom_Ri x hf))

theorem endpoint4 (x : Fin 5 → K) (hf : value x program.factor=0) :
    actualD (C x) (E x)*actualR02 (C x) (E x) = C x*(actualR4 (C x) (E x))^2 := by
  have h := checked_endpoint x program hf checked_program 182 184 DtimesR02Expr ctimesR4sqExpr DtimesR02_binding ctimesR4sq_binding endpoint4_same_nf
  simpa only [DtimesR02_expr_value x hf, ctimesR4sq_expr_value x hf] using h

theorem endpoint5 (x : Fin 5 → K) (hf : value x program.factor=0) : Vi x = (Ay x)^15*(Di x)^2/(5^30 : K) := by
  have h := matchesExpr_sound x program (program_law x hf) objectiveFormulaExpr 194 objectiveFormula_binding
  have hn : nodeValue x program 194 = nodeValue x program 195 := congrArg (meaning x) endpoint5_same_nf
  rw [objectiveFormula_expr_value x hf] at h
  exact ((h.symm.trans hn).trans (atom_Vi x hf)).symm

#print axioms checked_program
#print axioms endpoint4
#print axioms endpoint5
end N6.Even.ProgramData
