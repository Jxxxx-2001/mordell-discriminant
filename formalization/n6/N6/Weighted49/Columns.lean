import N6.Weighted49.ColumnSemantics000
import N6.Weighted49.ColumnSemantics001
import N6.Weighted49.ColumnSemantics002
import N6.Weighted49.ColumnSemantics003
import N6.Weighted49.ColumnSemantics004
import N6.Weighted49.ColumnSemantics005
import N6.Weighted49.ColumnSemantics006
import N6.Weighted49.ColumnSemantics007
import N6.Weighted49.ColumnSemantics008
import N6.Weighted49.ColumnSemantics009
import N6.Weighted49.ColumnSemantics010
import N6.Weighted49.ColumnSemantics011
import N6.Weighted49.ColumnSemantics012
import N6.Weighted49.ColumnSemantics013
import N6.Weighted49.ColumnSemantics014
import N6.Weighted49.ColumnSemantics015
import N6.Weighted49.ColumnSemantics016
import N6.Weighted49.ColumnSemantics017
import N6.Weighted49.ColumnSemantics018
import N6.Weighted49.ColumnSemantics019
import N6.Weighted49.ColumnSemantics020
import N6.Weighted49.ColumnSemantics021
import N6.Weighted49.ColumnSemantics022
import N6.Weighted49.ColumnSemantics023
import N6.Weighted49.ColumnSemantics024
import Mathlib.Data.Fintype.Fin
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem matrix_e_columns {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    ∀ j : Fin 49, (matrix_eDen : R) * x 1 * value x (basisData j) = W (fun i => value x (basisData i)) (fun i => matrix_e i j) := by
  intro j
  fin_cases j
  · exact column000_identity x hWA
  · exact column001_identity x hWA
  · exact column002_identity x hWA
  · exact column003_identity x hWA
  · exact column004_identity x hWA
  · exact column005_identity x hWA
  · exact column006_identity x hWA
  · exact column007_identity x hWA
  · exact column008_identity x hWA
  · exact column009_identity x hWA
  · exact column010_identity x hWA
  · exact column011_identity x hWA
  · exact column012_identity x hWA
  · exact column013_identity x hWA
  · exact column014_identity x hWA
  · exact column015_identity x hWA
  · exact column016_identity x hWA
  · exact column017_identity x hWA
  · exact column018_identity x hWA
  · exact column019_identity x hWA
  · exact column020_identity x hWA
  · exact column021_identity x hWA
  · exact column022_identity x hWA
  · exact column023_identity x hWA
  · exact column024_identity x hWA
  · exact column025_identity x hWA
  · exact column026_identity x hWA
  · exact column027_identity x hWA
  · exact column028_identity x hWA
  · exact column029_identity x hWA
  · exact column030_identity x hWA
  · exact column031_identity x hWA
  · exact column032_identity x hWA
  · exact column033_identity x hWA
  · exact column034_identity x hWA
  · exact column035_identity x hWA
  · exact column036_identity x hWA
  · exact column037_identity x hWA
  · exact column038_identity x hWA
  · exact column039_identity x hWA
  · exact column040_identity x hWA
  · exact column041_identity x hWA
  · exact column042_identity x hWA
  · exact column043_identity x hWA
  · exact column044_identity x hWA
  · exact column045_identity x hWA
  · exact column046_identity x hWA
  · exact column047_identity x hWA
  · exact column048_identity x hWA
#print axioms matrix_e_columns
theorem matrix_k_columns {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    ∀ j : Fin 49, (matrix_kDen : R) * x 2 * value x (basisData j) = W (fun i => value x (basisData i)) (fun i => matrix_k i j) := by
  intro j
  fin_cases j
  · exact column049_identity x hWA
  · exact column050_identity x hWA
  · exact column051_identity x hWA
  · exact column052_identity x hWA
  · exact column053_identity x hWA
  · exact column054_identity x hWA
  · exact column055_identity x hWA
  · exact column056_identity x hWA
  · exact column057_identity x hWA
  · exact column058_identity x hWA
  · exact column059_identity x hWA
  · exact column060_identity x hWA
  · exact column061_identity x hWA
  · exact column062_identity x hWA
  · exact column063_identity x hWA
  · exact column064_identity x hWA
  · exact column065_identity x hWA
  · exact column066_identity x hWA
  · exact column067_identity x hWA
  · exact column068_identity x hWA
  · exact column069_identity x hWA
  · exact column070_identity x hWA
  · exact column071_identity x hWA
  · exact column072_identity x hWA
  · exact column073_identity x hWA
  · exact column074_identity x hWA
  · exact column075_identity x hWA
  · exact column076_identity x hWA
  · exact column077_identity x hWA
  · exact column078_identity x hWA
  · exact column079_identity x hWA
  · exact column080_identity x hWA
  · exact column081_identity x hWA
  · exact column082_identity x hWA
  · exact column083_identity x hWA
  · exact column084_identity x hWA
  · exact column085_identity x hWA
  · exact column086_identity x hWA
  · exact column087_identity x hWA
  · exact column088_identity x hWA
  · exact column089_identity x hWA
  · exact column090_identity x hWA
  · exact column091_identity x hWA
  · exact column092_identity x hWA
  · exact column093_identity x hWA
  · exact column094_identity x hWA
  · exact column095_identity x hWA
  · exact column096_identity x hWA
  · exact column097_identity x hWA
#print axioms matrix_k_columns
theorem matrix_c_columns {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    ∀ j : Fin 49, (matrix_cDen : R) * x 3 * value x (basisData j) = W (fun i => value x (basisData i)) (fun i => matrix_c i j) := by
  intro j
  fin_cases j
  · exact column098_identity x hWA
  · exact column099_identity x hWA
  · exact column100_identity x hWA
  · exact column101_identity x hWA
  · exact column102_identity x hWA
  · exact column103_identity x hWA
  · exact column104_identity x hWA
  · exact column105_identity x hWA
  · exact column106_identity x hWA
  · exact column107_identity x hWA
  · exact column108_identity x hWA
  · exact column109_identity x hWA
  · exact column110_identity x hWA
  · exact column111_identity x hWA
  · exact column112_identity x hWA
  · exact column113_identity x hWA
  · exact column114_identity x hWA
  · exact column115_identity x hWA
  · exact column116_identity x hWA
  · exact column117_identity x hWA
  · exact column118_identity x hWA
  · exact column119_identity x hWA
  · exact column120_identity x hWA
  · exact column121_identity x hWA
  · exact column122_identity x hWA
  · exact column123_identity x hWA
  · exact column124_identity x hWA
  · exact column125_identity x hWA
  · exact column126_identity x hWA
  · exact column127_identity x hWA
  · exact column128_identity x hWA
  · exact column129_identity x hWA
  · exact column130_identity x hWA
  · exact column131_identity x hWA
  · exact column132_identity x hWA
  · exact column133_identity x hWA
  · exact column134_identity x hWA
  · exact column135_identity x hWA
  · exact column136_identity x hWA
  · exact column137_identity x hWA
  · exact column138_identity x hWA
  · exact column139_identity x hWA
  · exact column140_identity x hWA
  · exact column141_identity x hWA
  · exact column142_identity x hWA
  · exact column143_identity x hWA
  · exact column144_identity x hWA
  · exact column145_identity x hWA
  · exact column146_identity x hWA
#print axioms matrix_c_columns
theorem matrix_B_columns {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    ∀ j : Fin 49, (matrix_BDen : R) * x 4 * value x (basisData j) = W (fun i => value x (basisData i)) (fun i => matrix_B i j) := by
  intro j
  fin_cases j
  · exact column147_identity x hWA
  · exact column148_identity x hWA
  · exact column149_identity x hWA
  · exact column150_identity x hWA
  · exact column151_identity x hWA
  · exact column152_identity x hWA
  · exact column153_identity x hWA
  · exact column154_identity x hWA
  · exact column155_identity x hWA
  · exact column156_identity x hWA
  · exact column157_identity x hWA
  · exact column158_identity x hWA
  · exact column159_identity x hWA
  · exact column160_identity x hWA
  · exact column161_identity x hWA
  · exact column162_identity x hWA
  · exact column163_identity x hWA
  · exact column164_identity x hWA
  · exact column165_identity x hWA
  · exact column166_identity x hWA
  · exact column167_identity x hWA
  · exact column168_identity x hWA
  · exact column169_identity x hWA
  · exact column170_identity x hWA
  · exact column171_identity x hWA
  · exact column172_identity x hWA
  · exact column173_identity x hWA
  · exact column174_identity x hWA
  · exact column175_identity x hWA
  · exact column176_identity x hWA
  · exact column177_identity x hWA
  · exact column178_identity x hWA
  · exact column179_identity x hWA
  · exact column180_identity x hWA
  · exact column181_identity x hWA
  · exact column182_identity x hWA
  · exact column183_identity x hWA
  · exact column184_identity x hWA
  · exact column185_identity x hWA
  · exact column186_identity x hWA
  · exact column187_identity x hWA
  · exact column188_identity x hWA
  · exact column189_identity x hWA
  · exact column190_identity x hWA
  · exact column191_identity x hWA
  · exact column192_identity x hWA
  · exact column193_identity x hWA
  · exact column194_identity x hWA
  · exact column195_identity x hWA
#print axioms matrix_B_columns
end N6.Weighted49
