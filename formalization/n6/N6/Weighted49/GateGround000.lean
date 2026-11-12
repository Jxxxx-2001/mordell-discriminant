import N6.Weighted49.VecData
import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ColumnCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem unitVectorChecked : ∀ i : Fin 49, vec_M000 i = if i = 0 then 1 else 0 := by decide +kernel
theorem step000_nonzero : step000Left ≠ 0 := by decide +kernel
theorem step000_scale : step000Left * den_M001 = step000Right * matrix_BDen * den_M000 := by decide +kernel
theorem step000_list : scaleList step000Left vec_M001Data.toList = scaleList step000Right (foldColumns 49 vec_M000Data.toList FullLists.B) := by decide +kernel
theorem step000_monomial : mon_M001 = mon_M000.plus (variableMon 4) := by decide +kernel
#print axioms step000_list
theorem step001_nonzero : step001Left ≠ 0 := by decide +kernel
theorem step001_scale : step001Left * den_M002 = step001Right * matrix_cDen * den_M000 := by decide +kernel
theorem step001_list : scaleList step001Left vec_M002Data.toList = scaleList step001Right (foldColumns 49 vec_M000Data.toList FullLists.c) := by decide +kernel
theorem step001_monomial : mon_M002 = mon_M000.plus (variableMon 3) := by decide +kernel
#print axioms step001_list
theorem step002_nonzero : step002Left ≠ 0 := by decide +kernel
theorem step002_scale : step002Left * den_M003 = step002Right * matrix_eDen * den_M000 := by decide +kernel
theorem step002_list : scaleList step002Left vec_M003Data.toList = scaleList step002Right (foldColumns 49 vec_M000Data.toList FullLists.e) := by decide +kernel
theorem step002_monomial : mon_M003 = mon_M000.plus (variableMon 1) := by decide +kernel
#print axioms step002_list
theorem step003_nonzero : step003Left ≠ 0 := by decide +kernel
theorem step003_scale : step003Left * den_M004 = step003Right * matrix_BDen * den_M001 := by decide +kernel
theorem step003_list : scaleList step003Left vec_M004Data.toList = scaleList step003Right (foldColumns 49 vec_M001Data.toList FullLists.B) := by decide +kernel
theorem step003_monomial : mon_M004 = mon_M001.plus (variableMon 4) := by decide +kernel
#print axioms step003_list
theorem step004_nonzero : step004Left ≠ 0 := by decide +kernel
theorem step004_scale : step004Left * den_M005 = step004Right * matrix_cDen * den_M001 := by decide +kernel
theorem step004_list : scaleList step004Left vec_M005Data.toList = scaleList step004Right (foldColumns 49 vec_M001Data.toList FullLists.c) := by decide +kernel
theorem step004_monomial : mon_M005 = mon_M001.plus (variableMon 3) := by decide +kernel
#print axioms step004_list
theorem step005_nonzero : step005Left ≠ 0 := by decide +kernel
theorem step005_scale : step005Left * den_M006 = step005Right * matrix_cDen * den_M002 := by decide +kernel
theorem step005_list : scaleList step005Left vec_M006Data.toList = scaleList step005Right (foldColumns 49 vec_M002Data.toList FullLists.c) := by decide +kernel
theorem step005_monomial : mon_M006 = mon_M002.plus (variableMon 3) := by decide +kernel
#print axioms step005_list
theorem step006_nonzero : step006Left ≠ 0 := by decide +kernel
theorem step006_scale : step006Left * den_M007 = step006Right * matrix_kDen * den_M001 := by decide +kernel
theorem step006_list : scaleList step006Left vec_M007Data.toList = scaleList step006Right (foldColumns 49 vec_M001Data.toList FullLists.k) := by decide +kernel
theorem step006_monomial : mon_M007 = mon_M001.plus (variableMon 2) := by decide +kernel
#print axioms step006_list
theorem step007_nonzero : step007Left ≠ 0 := by decide +kernel
theorem step007_scale : step007Left * den_M008 = step007Right * matrix_eDen * den_M001 := by decide +kernel
theorem step007_list : scaleList step007Left vec_M008Data.toList = scaleList step007Right (foldColumns 49 vec_M001Data.toList FullLists.e) := by decide +kernel
theorem step007_monomial : mon_M008 = mon_M001.plus (variableMon 1) := by decide +kernel
#print axioms step007_list
theorem step008_nonzero : step008Left ≠ 0 := by decide +kernel
theorem step008_scale : step008Left * den_M009 = step008Right * matrix_eDen * den_M002 := by decide +kernel
theorem step008_list : scaleList step008Left vec_M009Data.toList = scaleList step008Right (foldColumns 49 vec_M002Data.toList FullLists.e) := by decide +kernel
theorem step008_monomial : mon_M009 = mon_M002.plus (variableMon 1) := by decide +kernel
#print axioms step008_list
theorem step009_nonzero : step009Left ≠ 0 := by decide +kernel
theorem step009_scale : step009Left * den_M010 = step009Right * matrix_eDen * den_M003 := by decide +kernel
theorem step009_list : scaleList step009Left vec_M010Data.toList = scaleList step009Right (foldColumns 49 vec_M003Data.toList FullLists.e) := by decide +kernel
theorem step009_monomial : mon_M010 = mon_M003.plus (variableMon 1) := by decide +kernel
#print axioms step009_list
theorem step010_nonzero : step010Left ≠ 0 := by decide +kernel
theorem step010_scale : step010Left * den_M011 = step010Right * matrix_BDen * den_M004 := by decide +kernel
theorem step010_list : scaleList step010Left vec_M011Data.toList = scaleList step010Right (foldColumns 49 vec_M004Data.toList FullLists.B) := by decide +kernel
theorem step010_monomial : mon_M011 = mon_M004.plus (variableMon 4) := by decide +kernel
#print axioms step010_list
theorem step011_nonzero : step011Left ≠ 0 := by decide +kernel
theorem step011_scale : step011Left * den_M012 = step011Right * matrix_cDen * den_M004 := by decide +kernel
theorem step011_list : scaleList step011Left vec_M012Data.toList = scaleList step011Right (foldColumns 49 vec_M004Data.toList FullLists.c) := by decide +kernel
theorem step011_monomial : mon_M012 = mon_M004.plus (variableMon 3) := by decide +kernel
#print axioms step011_list
theorem step012_nonzero : step012Left ≠ 0 := by decide +kernel
theorem step012_scale : step012Left * den_M013 = step012Right * matrix_cDen * den_M005 := by decide +kernel
theorem step012_list : scaleList step012Left vec_M013Data.toList = scaleList step012Right (foldColumns 49 vec_M005Data.toList FullLists.c) := by decide +kernel
theorem step012_monomial : mon_M013 = mon_M005.plus (variableMon 3) := by decide +kernel
#print axioms step012_list
theorem step013_nonzero : step013Left ≠ 0 := by decide +kernel
theorem step013_scale : step013Left * den_M014 = step013Right * matrix_cDen * den_M006 := by decide +kernel
theorem step013_list : scaleList step013Left vec_M014Data.toList = scaleList step013Right (foldColumns 49 vec_M006Data.toList FullLists.c) := by decide +kernel
theorem step013_monomial : mon_M014 = mon_M006.plus (variableMon 3) := by decide +kernel
#print axioms step013_list
theorem step014_nonzero : step014Left ≠ 0 := by decide +kernel
theorem step014_scale : step014Left * den_M015 = step014Right * matrix_kDen * den_M004 := by decide +kernel
theorem step014_list : scaleList step014Left vec_M015Data.toList = scaleList step014Right (foldColumns 49 vec_M004Data.toList FullLists.k) := by decide +kernel
theorem step014_monomial : mon_M015 = mon_M004.plus (variableMon 2) := by decide +kernel
#print axioms step014_list
theorem step015_nonzero : step015Left ≠ 0 := by decide +kernel
theorem step015_scale : step015Left * den_M016 = step015Right * matrix_kDen * den_M005 := by decide +kernel
theorem step015_list : scaleList step015Left vec_M016Data.toList = scaleList step015Right (foldColumns 49 vec_M005Data.toList FullLists.k) := by decide +kernel
theorem step015_monomial : mon_M016 = mon_M005.plus (variableMon 2) := by decide +kernel
#print axioms step015_list
end N6.Weighted49
