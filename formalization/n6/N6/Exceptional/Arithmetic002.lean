import N6.Exceptional.ArithmeticHelpers
import N6.Exceptional.Ground002
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
def entriesA033 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A40
  | _ => value x A45
def entriesH033 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H40
  | _ => value x H45
def childD033 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D032
  | _ => value x D001
def childJ033 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J032
  | _ => value x J001
theorem const_identity033 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D033 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA033 x j * childD033 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs033 constChecked033
  simp only [constPairs033, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D033 = ((-1 : R)^0 * (value x A40) * (value x D032) + ((-1 : R)^1 * (value x A45) * (value x D001) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity033
theorem linear_identity033 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J033 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH033 x j * childD033 x j + entriesA033 x j * childJ033 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs033 linearChecked033
  simp only [linearPairs033, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J033 = ((-1 : R)^0 * ((value x H40) * (value x D032) + (value x A40) * (value x J032)) + ((-1 : R)^1 * ((value x H45) * (value x D001) + (value x A45) * (value x J001)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity033
def entriesA034 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A41
  | _ => value x A45
def entriesH034 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H41
  | _ => value x H45
def childD034 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D032
  | _ => value x D002
def childJ034 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J032
  | _ => value x J002
theorem const_identity034 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D034 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA034 x j * childD034 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs034 constChecked034
  simp only [constPairs034, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D034 = ((-1 : R)^0 * (value x A41) * (value x D032) + ((-1 : R)^1 * (value x A45) * (value x D002) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity034
theorem linear_identity034 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J034 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH034 x j * childD034 x j + entriesA034 x j * childJ034 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs034 linearChecked034
  simp only [linearPairs034, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J034 = ((-1 : R)^0 * ((value x H41) * (value x D032) + (value x A41) * (value x J032)) + ((-1 : R)^1 * ((value x H45) * (value x D002) + (value x A45) * (value x J002)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity034
def entriesA036 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A42
  | _ => value x A45
def entriesH036 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H42
  | _ => value x H45
def childD036 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D032
  | _ => value x D004
def childJ036 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J032
  | _ => value x J004
theorem const_identity036 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D036 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA036 x j * childD036 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs036 constChecked036
  simp only [constPairs036, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D036 = ((-1 : R)^0 * (value x A42) * (value x D032) + ((-1 : R)^1 * (value x A45) * (value x D004) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity036
theorem linear_identity036 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J036 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH036 x j * childD036 x j + entriesA036 x j * childJ036 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs036 linearChecked036
  simp only [linearPairs036, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J036 = ((-1 : R)^0 * ((value x H42) * (value x D032) + (value x A42) * (value x J032)) + ((-1 : R)^1 * ((value x H45) * (value x D004) + (value x A45) * (value x J004)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity036
def entriesA040 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A43
  | _ => value x A45
def entriesH040 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H43
  | _ => value x H45
def childD040 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D032
  | _ => value x D008
def childJ040 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J032
  | _ => value x J008
theorem const_identity040 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D040 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA040 x j * childD040 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs040 constChecked040
  simp only [constPairs040, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D040 = ((-1 : R)^0 * (value x A43) * (value x D032) + ((-1 : R)^1 * (value x A45) * (value x D008) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity040
theorem linear_identity040 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J040 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH040 x j * childD040 x j + entriesA040 x j * childJ040 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs040 linearChecked040
  simp only [linearPairs040, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J040 = ((-1 : R)^0 * ((value x H43) * (value x D032) + (value x A43) * (value x J032)) + ((-1 : R)^1 * ((value x H45) * (value x D008) + (value x A45) * (value x J008)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity040
def entriesA048 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A44
  | _ => value x A45
def entriesH048 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H44
  | _ => value x H45
def childD048 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D032
  | _ => value x D016
def childJ048 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J032
  | _ => value x J016
theorem const_identity048 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D048 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA048 x j * childD048 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs048 constChecked048
  simp only [constPairs048, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D048 = ((-1 : R)^0 * (value x A44) * (value x D032) + ((-1 : R)^1 * (value x A45) * (value x D016) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity048
theorem linear_identity048 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J048 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH048 x j * childD048 x j + entriesA048 x j * childJ048 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs048 linearChecked048
  simp only [linearPairs048, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J048 = ((-1 : R)^0 * ((value x H44) * (value x D032) + (value x A44) * (value x J032)) + ((-1 : R)^1 * ((value x H45) * (value x D016) + (value x A45) * (value x J016)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity048
def entriesA007 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A30
  | 1 => value x A31
  | _ => value x A32
def entriesH007 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H30
  | 1 => value x H31
  | _ => value x H32
def childD007 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D006
  | 1 => value x D005
  | _ => value x D003
def childJ007 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J006
  | 1 => value x J005
  | _ => value x J003
theorem const_identity007 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D007 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA007 x j * childD007 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs007 constChecked007
  simp only [constPairs007, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D007 = ((-1 : R)^0 * (value x A30) * (value x D006) + ((-1 : R)^1 * (value x A31) * (value x D005) + ((-1 : R)^2 * (value x A32) * (value x D003) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity007
theorem linear_identity007 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J007 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH007 x j * childD007 x j + entriesA007 x j * childJ007 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs007 linearChecked007
  simp only [linearPairs007, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J007 = ((-1 : R)^0 * ((value x H30) * (value x D006) + (value x A30) * (value x J006)) + ((-1 : R)^1 * ((value x H31) * (value x D005) + (value x A31) * (value x J005)) + ((-1 : R)^2 * ((value x H32) * (value x D003) + (value x A32) * (value x J003)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity007
def entriesA011 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A30
  | 1 => value x A31
  | _ => value x A33
def entriesH011 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H30
  | 1 => value x H31
  | _ => value x H33
def childD011 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D010
  | 1 => value x D009
  | _ => value x D003
def childJ011 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J010
  | 1 => value x J009
  | _ => value x J003
theorem const_identity011 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D011 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA011 x j * childD011 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs011 constChecked011
  simp only [constPairs011, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D011 = ((-1 : R)^0 * (value x A30) * (value x D010) + ((-1 : R)^1 * (value x A31) * (value x D009) + ((-1 : R)^2 * (value x A33) * (value x D003) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity011
theorem linear_identity011 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J011 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH011 x j * childD011 x j + entriesA011 x j * childJ011 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs011 linearChecked011
  simp only [linearPairs011, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J011 = ((-1 : R)^0 * ((value x H30) * (value x D010) + (value x A30) * (value x J010)) + ((-1 : R)^1 * ((value x H31) * (value x D009) + (value x A31) * (value x J009)) + ((-1 : R)^2 * ((value x H33) * (value x D003) + (value x A33) * (value x J003)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity011
def entriesA013 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A30
  | 1 => value x A32
  | _ => value x A33
def entriesH013 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H30
  | 1 => value x H32
  | _ => value x H33
def childD013 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D012
  | 1 => value x D009
  | _ => value x D005
def childJ013 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J012
  | 1 => value x J009
  | _ => value x J005
theorem const_identity013 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D013 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA013 x j * childD013 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs013 constChecked013
  simp only [constPairs013, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D013 = ((-1 : R)^0 * (value x A30) * (value x D012) + ((-1 : R)^1 * (value x A32) * (value x D009) + ((-1 : R)^2 * (value x A33) * (value x D005) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity013
theorem linear_identity013 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J013 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH013 x j * childD013 x j + entriesA013 x j * childJ013 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs013 linearChecked013
  simp only [linearPairs013, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J013 = ((-1 : R)^0 * ((value x H30) * (value x D012) + (value x A30) * (value x J012)) + ((-1 : R)^1 * ((value x H32) * (value x D009) + (value x A32) * (value x J009)) + ((-1 : R)^2 * ((value x H33) * (value x D005) + (value x A33) * (value x J005)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity013
end N6.Exceptional
