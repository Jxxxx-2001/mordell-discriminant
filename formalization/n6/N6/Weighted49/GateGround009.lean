import N6.Weighted49.VecData
import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ColumnCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step145_nonzero : step145Left ≠ 0 := by decide +kernel
theorem step145_scale : step145Left * den_K006 = step145Right * matrix_BDen * den_K005 := by decide +kernel
theorem step145_list : scaleList step145Left vec_K006Data.toList = scaleList step145Right (foldColumns 49 vec_K005Data.toList FullLists.B) := by decide +kernel
#print axioms step145_list
theorem step146_nonzero : step146Left ≠ 0 := by decide +kernel
theorem step146_scale : step146Left * den_K007 = step146Right * matrix_BDen * den_K006 := by decide +kernel
theorem step146_list : scaleList step146Left vec_K007Data.toList = scaleList step146Right (foldColumns 49 vec_K006Data.toList FullLists.B) := by decide +kernel
#print axioms step146_list
theorem step147_nonzero : step147Left ≠ 0 := by decide +kernel
theorem step147_scale : step147Left * den_K008 = step147Right * matrix_BDen * den_K007 := by decide +kernel
theorem step147_list : scaleList step147Left vec_K008Data.toList = scaleList step147Right (foldColumns 49 vec_K007Data.toList FullLists.B) := by decide +kernel
#print axioms step147_list
theorem step148_nonzero : step148Left ≠ 0 := by decide +kernel
theorem step148_scale : step148Left * den_K009 = step148Right * matrix_BDen * den_K008 := by decide +kernel
theorem step148_list : scaleList step148Left vec_K009Data.toList = scaleList step148Right (foldColumns 49 vec_K008Data.toList FullLists.B) := by decide +kernel
#print axioms step148_list
theorem step149_nonzero : step149Left ≠ 0 := by decide +kernel
theorem step149_scale : step149Left * den_K010 = step149Right * matrix_BDen * den_K009 := by decide +kernel
theorem step149_list : scaleList step149Left vec_K010Data.toList = scaleList step149Right (foldColumns 49 vec_K009Data.toList FullLists.B) := by decide +kernel
#print axioms step149_list
theorem step150_nonzero : step150Left ≠ 0 := by decide +kernel
theorem step150_scale : step150Left * den_K011 = step150Right * matrix_BDen * den_K010 := by decide +kernel
theorem step150_list : scaleList step150Left vec_K011Data.toList = scaleList step150Right (foldColumns 49 vec_K010Data.toList FullLists.B) := by decide +kernel
#print axioms step150_list
theorem step151_nonzero : step151Left ≠ 0 := by decide +kernel
theorem step151_scale : step151Left * den_K012 = step151Right * matrix_BDen * den_K011 := by decide +kernel
theorem step151_list : scaleList step151Left vec_K012Data.toList = scaleList step151Right (foldColumns 49 vec_K011Data.toList FullLists.B) := by decide +kernel
#print axioms step151_list
theorem step152_nonzero : step152Left ≠ 0 := by decide +kernel
theorem step152_scale : step152Left * den_K013 = step152Right * matrix_BDen * den_K012 := by decide +kernel
theorem step152_list : scaleList step152Left vec_K013Data.toList = scaleList step152Right (foldColumns 49 vec_K012Data.toList FullLists.B) := by decide +kernel
#print axioms step152_list
theorem step153_nonzero : step153Left ≠ 0 := by decide +kernel
theorem step153_scale : step153Left * den_K014 = step153Right * matrix_BDen * den_K013 := by decide +kernel
theorem step153_list : scaleList step153Left vec_K014Data.toList = scaleList step153Right (foldColumns 49 vec_K013Data.toList FullLists.B) := by decide +kernel
#print axioms step153_list
theorem step154_nonzero : step154Left ≠ 0 := by decide +kernel
theorem step154_scale : step154Left * den_K015 = step154Right * matrix_BDen * den_K014 := by decide +kernel
theorem step154_list : scaleList step154Left vec_K015Data.toList = scaleList step154Right (foldColumns 49 vec_K014Data.toList FullLists.B) := by decide +kernel
#print axioms step154_list
theorem step155_nonzero : step155Left ≠ 0 := by decide +kernel
theorem step155_scale : step155Left * den_K016 = step155Right * matrix_BDen * den_K015 := by decide +kernel
theorem step155_list : scaleList step155Left vec_K016Data.toList = scaleList step155Right (foldColumns 49 vec_K015Data.toList FullLists.B) := by decide +kernel
#print axioms step155_list
theorem step156_nonzero : step156Left ≠ 0 := by decide +kernel
theorem step156_scale : step156Left * den_K017 = step156Right * matrix_BDen * den_K016 := by decide +kernel
theorem step156_list : scaleList step156Left vec_K017Data.toList = scaleList step156Right (foldColumns 49 vec_K016Data.toList FullLists.B) := by decide +kernel
#print axioms step156_list
theorem step157_nonzero : step157Left ≠ 0 := by decide +kernel
theorem step157_scale : step157Left * den_K018 = step157Right * matrix_BDen * den_K017 := by decide +kernel
theorem step157_list : scaleList step157Left vec_K018Data.toList = scaleList step157Right (foldColumns 49 vec_K017Data.toList FullLists.B) := by decide +kernel
#print axioms step157_list
theorem step158_nonzero : step158Left ≠ 0 := by decide +kernel
theorem step158_scale : step158Left * den_K019 = step158Right * matrix_BDen * den_K018 := by decide +kernel
theorem step158_list : scaleList step158Left vec_K019Data.toList = scaleList step158Right (foldColumns 49 vec_K018Data.toList FullLists.B) := by decide +kernel
#print axioms step158_list
theorem step159_nonzero : step159Left ≠ 0 := by decide +kernel
theorem step159_scale : step159Left * den_K020 = step159Right * matrix_BDen * den_K019 := by decide +kernel
theorem step159_list : scaleList step159Left vec_K020Data.toList = scaleList step159Right (foldColumns 49 vec_K019Data.toList FullLists.B) := by decide +kernel
#print axioms step159_list
theorem step160_nonzero : step160Left ≠ 0 := by decide +kernel
theorem step160_scale : step160Left * den_K021 = step160Right * matrix_BDen * den_K020 := by decide +kernel
theorem step160_list : scaleList step160Left vec_K021Data.toList = scaleList step160Right (foldColumns 49 vec_K020Data.toList FullLists.B) := by decide +kernel
#print axioms step160_list
end N6.Weighted49
