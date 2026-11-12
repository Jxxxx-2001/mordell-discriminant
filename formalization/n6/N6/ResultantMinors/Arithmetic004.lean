import N6.ResultantMinors.ArithmeticHelpers
import N6.ResultantMinors.Ground004
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace N6.ResultantMinors
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
def entriesA037 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A30
  | 1 => value x A32
  | _ => value x A35
def entriesH037 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H30
  | 1 => value x H32
  | _ => value x H35
def childD037 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D036
  | 1 => value x D033
  | _ => value x D005
def childJ037 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J036
  | 1 => value x J033
  | _ => value x J005
theorem const_identity037 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D037 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA037 x j * childD037 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs037 constChecked037
  simp only [constPairs037, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D037 = ((-1 : R)^0 * (value x A30) * (value x D036) + ((-1 : R)^1 * (value x A32) * (value x D033) + ((-1 : R)^2 * (value x A35) * (value x D005) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity037
theorem linear_identity037 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J037 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH037 x j * childD037 x j + entriesA037 x j * childJ037 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs037 linearChecked037
  simp only [linearPairs037, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J037 = ((-1 : R)^0 * ((value x H30) * (value x D036) + (value x A30) * (value x J036)) + ((-1 : R)^1 * ((value x H32) * (value x D033) + (value x A32) * (value x J033)) + ((-1 : R)^2 * ((value x H35) * (value x D005) + (value x A35) * (value x J005)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity037
def entriesA038 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A31
  | 1 => value x A32
  | _ => value x A35
def entriesH038 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H31
  | 1 => value x H32
  | _ => value x H35
def childD038 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D036
  | 1 => value x D034
  | _ => value x D006
def childJ038 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J036
  | 1 => value x J034
  | _ => value x J006
theorem const_identity038 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D038 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA038 x j * childD038 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs038 constChecked038
  simp only [constPairs038, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D038 = ((-1 : R)^0 * (value x A31) * (value x D036) + ((-1 : R)^1 * (value x A32) * (value x D034) + ((-1 : R)^2 * (value x A35) * (value x D006) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity038
theorem linear_identity038 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J038 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH038 x j * childD038 x j + entriesA038 x j * childJ038 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs038 linearChecked038
  simp only [linearPairs038, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J038 = ((-1 : R)^0 * ((value x H31) * (value x D036) + (value x A31) * (value x J036)) + ((-1 : R)^1 * ((value x H32) * (value x D034) + (value x A32) * (value x J034)) + ((-1 : R)^2 * ((value x H35) * (value x D006) + (value x A35) * (value x J006)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity038
def entriesA041 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A30
  | 1 => value x A33
  | _ => value x A35
def entriesH041 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H30
  | 1 => value x H33
  | _ => value x H35
def childD041 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D040
  | 1 => value x D033
  | _ => value x D009
def childJ041 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J040
  | 1 => value x J033
  | _ => value x J009
theorem const_identity041 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D041 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA041 x j * childD041 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs041 constChecked041
  simp only [constPairs041, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D041 = ((-1 : R)^0 * (value x A30) * (value x D040) + ((-1 : R)^1 * (value x A33) * (value x D033) + ((-1 : R)^2 * (value x A35) * (value x D009) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity041
theorem linear_identity041 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J041 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH041 x j * childD041 x j + entriesA041 x j * childJ041 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs041 linearChecked041
  simp only [linearPairs041, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J041 = ((-1 : R)^0 * ((value x H30) * (value x D040) + (value x A30) * (value x J040)) + ((-1 : R)^1 * ((value x H33) * (value x D033) + (value x A33) * (value x J033)) + ((-1 : R)^2 * ((value x H35) * (value x D009) + (value x A35) * (value x J009)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity041
def entriesA042 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A31
  | 1 => value x A33
  | _ => value x A35
def entriesH042 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H31
  | 1 => value x H33
  | _ => value x H35
def childD042 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D040
  | 1 => value x D034
  | _ => value x D010
def childJ042 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J040
  | 1 => value x J034
  | _ => value x J010
theorem const_identity042 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D042 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA042 x j * childD042 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs042 constChecked042
  simp only [constPairs042, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D042 = ((-1 : R)^0 * (value x A31) * (value x D040) + ((-1 : R)^1 * (value x A33) * (value x D034) + ((-1 : R)^2 * (value x A35) * (value x D010) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity042
theorem linear_identity042 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J042 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH042 x j * childD042 x j + entriesA042 x j * childJ042 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs042 linearChecked042
  simp only [linearPairs042, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J042 = ((-1 : R)^0 * ((value x H31) * (value x D040) + (value x A31) * (value x J040)) + ((-1 : R)^1 * ((value x H33) * (value x D034) + (value x A33) * (value x J034)) + ((-1 : R)^2 * ((value x H35) * (value x D010) + (value x A35) * (value x J010)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity042
def entriesA044 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A32
  | 1 => value x A33
  | _ => value x A35
def entriesH044 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H32
  | 1 => value x H33
  | _ => value x H35
def childD044 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D040
  | 1 => value x D036
  | _ => value x D012
def childJ044 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J040
  | 1 => value x J036
  | _ => value x J012
theorem const_identity044 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D044 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA044 x j * childD044 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs044 constChecked044
  simp only [constPairs044, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D044 = ((-1 : R)^0 * (value x A32) * (value x D040) + ((-1 : R)^1 * (value x A33) * (value x D036) + ((-1 : R)^2 * (value x A35) * (value x D012) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity044
theorem linear_identity044 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J044 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH044 x j * childD044 x j + entriesA044 x j * childJ044 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs044 linearChecked044
  simp only [linearPairs044, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J044 = ((-1 : R)^0 * ((value x H32) * (value x D040) + (value x A32) * (value x J040)) + ((-1 : R)^1 * ((value x H33) * (value x D036) + (value x A33) * (value x J036)) + ((-1 : R)^2 * ((value x H35) * (value x D012) + (value x A35) * (value x J012)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity044
def entriesA049 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A30
  | 1 => value x A34
  | _ => value x A35
def entriesH049 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H30
  | 1 => value x H34
  | _ => value x H35
def childD049 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D048
  | 1 => value x D033
  | _ => value x D017
def childJ049 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J048
  | 1 => value x J033
  | _ => value x J017
theorem const_identity049 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D049 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA049 x j * childD049 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs049 constChecked049
  simp only [constPairs049, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D049 = ((-1 : R)^0 * (value x A30) * (value x D048) + ((-1 : R)^1 * (value x A34) * (value x D033) + ((-1 : R)^2 * (value x A35) * (value x D017) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity049
theorem linear_identity049 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J049 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH049 x j * childD049 x j + entriesA049 x j * childJ049 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs049 linearChecked049
  simp only [linearPairs049, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J049 = ((-1 : R)^0 * ((value x H30) * (value x D048) + (value x A30) * (value x J048)) + ((-1 : R)^1 * ((value x H34) * (value x D033) + (value x A34) * (value x J033)) + ((-1 : R)^2 * ((value x H35) * (value x D017) + (value x A35) * (value x J017)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity049
def entriesA050 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A31
  | 1 => value x A34
  | _ => value x A35
def entriesH050 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H31
  | 1 => value x H34
  | _ => value x H35
def childD050 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D048
  | 1 => value x D034
  | _ => value x D018
def childJ050 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J048
  | 1 => value x J034
  | _ => value x J018
theorem const_identity050 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D050 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA050 x j * childD050 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs050 constChecked050
  simp only [constPairs050, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D050 = ((-1 : R)^0 * (value x A31) * (value x D048) + ((-1 : R)^1 * (value x A34) * (value x D034) + ((-1 : R)^2 * (value x A35) * (value x D018) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity050
theorem linear_identity050 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J050 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH050 x j * childD050 x j + entriesA050 x j * childJ050 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs050 linearChecked050
  simp only [linearPairs050, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J050 = ((-1 : R)^0 * ((value x H31) * (value x D048) + (value x A31) * (value x J048)) + ((-1 : R)^1 * ((value x H34) * (value x D034) + (value x A34) * (value x J034)) + ((-1 : R)^2 * ((value x H35) * (value x D018) + (value x A35) * (value x J018)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity050
def entriesA052 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A32
  | 1 => value x A34
  | _ => value x A35
def entriesH052 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H32
  | 1 => value x H34
  | _ => value x H35
def childD052 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D048
  | 1 => value x D036
  | _ => value x D020
def childJ052 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J048
  | 1 => value x J036
  | _ => value x J020
theorem const_identity052 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D052 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA052 x j * childD052 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs052 constChecked052
  simp only [constPairs052, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D052 = ((-1 : R)^0 * (value x A32) * (value x D048) + ((-1 : R)^1 * (value x A34) * (value x D036) + ((-1 : R)^2 * (value x A35) * (value x D020) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity052
theorem linear_identity052 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J052 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH052 x j * childD052 x j + entriesA052 x j * childJ052 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs052 linearChecked052
  simp only [linearPairs052, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J052 = ((-1 : R)^0 * ((value x H32) * (value x D048) + (value x A32) * (value x J048)) + ((-1 : R)^1 * ((value x H34) * (value x D036) + (value x A34) * (value x J036)) + ((-1 : R)^2 * ((value x H35) * (value x D020) + (value x A35) * (value x J020)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity052
end N6.ResultantMinors
