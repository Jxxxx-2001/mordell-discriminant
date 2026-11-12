import N6.ResultantMinors.ArithmeticHelpers
import N6.ResultantMinors.Ground003
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace N6.ResultantMinors
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
def entriesA014 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A31
  | 1 => value x A32
  | _ => value x A33
def entriesH014 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H31
  | 1 => value x H32
  | _ => value x H33
def childD014 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D012
  | 1 => value x D010
  | _ => value x D006
def childJ014 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J012
  | 1 => value x J010
  | _ => value x J006
theorem const_identity014 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D014 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA014 x j * childD014 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs014 constChecked014
  simp only [constPairs014, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D014 = ((-1 : R)^0 * (value x A31) * (value x D012) + ((-1 : R)^1 * (value x A32) * (value x D010) + ((-1 : R)^2 * (value x A33) * (value x D006) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity014
theorem linear_identity014 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J014 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH014 x j * childD014 x j + entriesA014 x j * childJ014 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs014 linearChecked014
  simp only [linearPairs014, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J014 = ((-1 : R)^0 * ((value x H31) * (value x D012) + (value x A31) * (value x J012)) + ((-1 : R)^1 * ((value x H32) * (value x D010) + (value x A32) * (value x J010)) + ((-1 : R)^2 * ((value x H33) * (value x D006) + (value x A33) * (value x J006)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity014
def entriesA019 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A30
  | 1 => value x A31
  | _ => value x A34
def entriesH019 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H30
  | 1 => value x H31
  | _ => value x H34
def childD019 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D018
  | 1 => value x D017
  | _ => value x D003
def childJ019 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J018
  | 1 => value x J017
  | _ => value x J003
theorem const_identity019 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D019 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA019 x j * childD019 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs019 constChecked019
  simp only [constPairs019, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D019 = ((-1 : R)^0 * (value x A30) * (value x D018) + ((-1 : R)^1 * (value x A31) * (value x D017) + ((-1 : R)^2 * (value x A34) * (value x D003) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity019
theorem linear_identity019 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J019 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH019 x j * childD019 x j + entriesA019 x j * childJ019 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs019 linearChecked019
  simp only [linearPairs019, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J019 = ((-1 : R)^0 * ((value x H30) * (value x D018) + (value x A30) * (value x J018)) + ((-1 : R)^1 * ((value x H31) * (value x D017) + (value x A31) * (value x J017)) + ((-1 : R)^2 * ((value x H34) * (value x D003) + (value x A34) * (value x J003)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity019
def entriesA021 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A30
  | 1 => value x A32
  | _ => value x A34
def entriesH021 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H30
  | 1 => value x H32
  | _ => value x H34
def childD021 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D020
  | 1 => value x D017
  | _ => value x D005
def childJ021 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J020
  | 1 => value x J017
  | _ => value x J005
theorem const_identity021 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D021 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA021 x j * childD021 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs021 constChecked021
  simp only [constPairs021, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D021 = ((-1 : R)^0 * (value x A30) * (value x D020) + ((-1 : R)^1 * (value x A32) * (value x D017) + ((-1 : R)^2 * (value x A34) * (value x D005) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity021
theorem linear_identity021 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J021 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH021 x j * childD021 x j + entriesA021 x j * childJ021 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs021 linearChecked021
  simp only [linearPairs021, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J021 = ((-1 : R)^0 * ((value x H30) * (value x D020) + (value x A30) * (value x J020)) + ((-1 : R)^1 * ((value x H32) * (value x D017) + (value x A32) * (value x J017)) + ((-1 : R)^2 * ((value x H34) * (value x D005) + (value x A34) * (value x J005)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity021
def entriesA022 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A31
  | 1 => value x A32
  | _ => value x A34
def entriesH022 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H31
  | 1 => value x H32
  | _ => value x H34
def childD022 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D020
  | 1 => value x D018
  | _ => value x D006
def childJ022 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J020
  | 1 => value x J018
  | _ => value x J006
theorem const_identity022 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D022 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA022 x j * childD022 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs022 constChecked022
  simp only [constPairs022, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D022 = ((-1 : R)^0 * (value x A31) * (value x D020) + ((-1 : R)^1 * (value x A32) * (value x D018) + ((-1 : R)^2 * (value x A34) * (value x D006) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity022
theorem linear_identity022 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J022 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH022 x j * childD022 x j + entriesA022 x j * childJ022 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs022 linearChecked022
  simp only [linearPairs022, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J022 = ((-1 : R)^0 * ((value x H31) * (value x D020) + (value x A31) * (value x J020)) + ((-1 : R)^1 * ((value x H32) * (value x D018) + (value x A32) * (value x J018)) + ((-1 : R)^2 * ((value x H34) * (value x D006) + (value x A34) * (value x J006)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity022
def entriesA025 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A30
  | 1 => value x A33
  | _ => value x A34
def entriesH025 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H30
  | 1 => value x H33
  | _ => value x H34
def childD025 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D024
  | 1 => value x D017
  | _ => value x D009
def childJ025 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J024
  | 1 => value x J017
  | _ => value x J009
theorem const_identity025 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D025 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA025 x j * childD025 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs025 constChecked025
  simp only [constPairs025, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D025 = ((-1 : R)^0 * (value x A30) * (value x D024) + ((-1 : R)^1 * (value x A33) * (value x D017) + ((-1 : R)^2 * (value x A34) * (value x D009) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity025
theorem linear_identity025 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J025 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH025 x j * childD025 x j + entriesA025 x j * childJ025 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs025 linearChecked025
  simp only [linearPairs025, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J025 = ((-1 : R)^0 * ((value x H30) * (value x D024) + (value x A30) * (value x J024)) + ((-1 : R)^1 * ((value x H33) * (value x D017) + (value x A33) * (value x J017)) + ((-1 : R)^2 * ((value x H34) * (value x D009) + (value x A34) * (value x J009)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity025
def entriesA026 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A31
  | 1 => value x A33
  | _ => value x A34
def entriesH026 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H31
  | 1 => value x H33
  | _ => value x H34
def childD026 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D024
  | 1 => value x D018
  | _ => value x D010
def childJ026 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J024
  | 1 => value x J018
  | _ => value x J010
theorem const_identity026 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D026 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA026 x j * childD026 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs026 constChecked026
  simp only [constPairs026, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D026 = ((-1 : R)^0 * (value x A31) * (value x D024) + ((-1 : R)^1 * (value x A33) * (value x D018) + ((-1 : R)^2 * (value x A34) * (value x D010) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity026
theorem linear_identity026 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J026 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH026 x j * childD026 x j + entriesA026 x j * childJ026 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs026 linearChecked026
  simp only [linearPairs026, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J026 = ((-1 : R)^0 * ((value x H31) * (value x D024) + (value x A31) * (value x J024)) + ((-1 : R)^1 * ((value x H33) * (value x D018) + (value x A33) * (value x J018)) + ((-1 : R)^2 * ((value x H34) * (value x D010) + (value x A34) * (value x J010)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity026
def entriesA028 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A32
  | 1 => value x A33
  | _ => value x A34
def entriesH028 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H32
  | 1 => value x H33
  | _ => value x H34
def childD028 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D024
  | 1 => value x D020
  | _ => value x D012
def childJ028 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J024
  | 1 => value x J020
  | _ => value x J012
theorem const_identity028 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D028 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA028 x j * childD028 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs028 constChecked028
  simp only [constPairs028, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D028 = ((-1 : R)^0 * (value x A32) * (value x D024) + ((-1 : R)^1 * (value x A33) * (value x D020) + ((-1 : R)^2 * (value x A34) * (value x D012) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity028
theorem linear_identity028 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J028 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH028 x j * childD028 x j + entriesA028 x j * childJ028 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs028 linearChecked028
  simp only [linearPairs028, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J028 = ((-1 : R)^0 * ((value x H32) * (value x D024) + (value x A32) * (value x J024)) + ((-1 : R)^1 * ((value x H33) * (value x D020) + (value x A33) * (value x J020)) + ((-1 : R)^2 * ((value x H34) * (value x D012) + (value x A34) * (value x J012)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity028
def entriesA035 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A30
  | 1 => value x A31
  | _ => value x A35
def entriesH035 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H30
  | 1 => value x H31
  | _ => value x H35
def childD035 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D034
  | 1 => value x D033
  | _ => value x D003
def childJ035 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J034
  | 1 => value x J033
  | _ => value x J003
theorem const_identity035 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D035 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA035 x j * childD035 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs035 constChecked035
  simp only [constPairs035, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D035 = ((-1 : R)^0 * (value x A30) * (value x D034) + ((-1 : R)^1 * (value x A31) * (value x D033) + ((-1 : R)^2 * (value x A35) * (value x D003) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity035
theorem linear_identity035 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J035 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH035 x j * childD035 x j + entriesA035 x j * childJ035 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs035 linearChecked035
  simp only [linearPairs035, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J035 = ((-1 : R)^0 * ((value x H30) * (value x D034) + (value x A30) * (value x J034)) + ((-1 : R)^1 * ((value x H31) * (value x D033) + (value x A31) * (value x J033)) + ((-1 : R)^2 * ((value x H35) * (value x D003) + (value x A35) * (value x J003)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity035
end N6.ResultantMinors
