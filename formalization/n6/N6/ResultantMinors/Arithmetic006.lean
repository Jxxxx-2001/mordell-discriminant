import N6.ResultantMinors.ArithmeticHelpers
import N6.ResultantMinors.Ground006
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace N6.ResultantMinors
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
def entriesA045 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A20
  | 1 => value x A22
  | 2 => value x A23
  | _ => value x A25
def entriesH045 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H20
  | 1 => value x H22
  | 2 => value x H23
  | _ => value x H25
def childD045 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D044
  | 1 => value x D041
  | 2 => value x D037
  | _ => value x D013
def childJ045 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J044
  | 1 => value x J041
  | 2 => value x J037
  | _ => value x J013
theorem const_identity045 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D045 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA045 x j * childD045 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs045 constChecked045
  simp only [constPairs045, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D045 = ((-1 : R)^0 * (value x A20) * (value x D044) + ((-1 : R)^1 * (value x A22) * (value x D041) + ((-1 : R)^2 * (value x A23) * (value x D037) + ((-1 : R)^3 * (value x A25) * (value x D013) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity045
theorem linear_identity045 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J045 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH045 x j * childD045 x j + entriesA045 x j * childJ045 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs045 linearChecked045
  simp only [linearPairs045, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J045 = ((-1 : R)^0 * ((value x H20) * (value x D044) + (value x A20) * (value x J044)) + ((-1 : R)^1 * ((value x H22) * (value x D041) + (value x A22) * (value x J041)) + ((-1 : R)^2 * ((value x H23) * (value x D037) + (value x A23) * (value x J037)) + ((-1 : R)^3 * ((value x H25) * (value x D013) + (value x A25) * (value x J013)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity045
def entriesA046 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A21
  | 1 => value x A22
  | 2 => value x A23
  | _ => value x A25
def entriesH046 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H21
  | 1 => value x H22
  | 2 => value x H23
  | _ => value x H25
def childD046 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D044
  | 1 => value x D042
  | 2 => value x D038
  | _ => value x D014
def childJ046 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J044
  | 1 => value x J042
  | 2 => value x J038
  | _ => value x J014
theorem const_identity046 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D046 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA046 x j * childD046 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs046 constChecked046
  simp only [constPairs046, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D046 = ((-1 : R)^0 * (value x A21) * (value x D044) + ((-1 : R)^1 * (value x A22) * (value x D042) + ((-1 : R)^2 * (value x A23) * (value x D038) + ((-1 : R)^3 * (value x A25) * (value x D014) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity046
theorem linear_identity046 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J046 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH046 x j * childD046 x j + entriesA046 x j * childJ046 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs046 linearChecked046
  simp only [linearPairs046, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J046 = ((-1 : R)^0 * ((value x H21) * (value x D044) + (value x A21) * (value x J044)) + ((-1 : R)^1 * ((value x H22) * (value x D042) + (value x A22) * (value x J042)) + ((-1 : R)^2 * ((value x H23) * (value x D038) + (value x A23) * (value x J038)) + ((-1 : R)^3 * ((value x H25) * (value x D014) + (value x A25) * (value x J014)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity046
def entriesA051 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A20
  | 1 => value x A21
  | 2 => value x A24
  | _ => value x A25
def entriesH051 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H20
  | 1 => value x H21
  | 2 => value x H24
  | _ => value x H25
def childD051 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D050
  | 1 => value x D049
  | 2 => value x D035
  | _ => value x D019
def childJ051 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J050
  | 1 => value x J049
  | 2 => value x J035
  | _ => value x J019
theorem const_identity051 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D051 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA051 x j * childD051 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs051 constChecked051
  simp only [constPairs051, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D051 = ((-1 : R)^0 * (value x A20) * (value x D050) + ((-1 : R)^1 * (value x A21) * (value x D049) + ((-1 : R)^2 * (value x A24) * (value x D035) + ((-1 : R)^3 * (value x A25) * (value x D019) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity051
theorem linear_identity051 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J051 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH051 x j * childD051 x j + entriesA051 x j * childJ051 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs051 linearChecked051
  simp only [linearPairs051, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J051 = ((-1 : R)^0 * ((value x H20) * (value x D050) + (value x A20) * (value x J050)) + ((-1 : R)^1 * ((value x H21) * (value x D049) + (value x A21) * (value x J049)) + ((-1 : R)^2 * ((value x H24) * (value x D035) + (value x A24) * (value x J035)) + ((-1 : R)^3 * ((value x H25) * (value x D019) + (value x A25) * (value x J019)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity051
def entriesA053 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A20
  | 1 => value x A22
  | 2 => value x A24
  | _ => value x A25
def entriesH053 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H20
  | 1 => value x H22
  | 2 => value x H24
  | _ => value x H25
def childD053 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D052
  | 1 => value x D049
  | 2 => value x D037
  | _ => value x D021
def childJ053 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J052
  | 1 => value x J049
  | 2 => value x J037
  | _ => value x J021
theorem const_identity053 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D053 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA053 x j * childD053 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs053 constChecked053
  simp only [constPairs053, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D053 = ((-1 : R)^0 * (value x A20) * (value x D052) + ((-1 : R)^1 * (value x A22) * (value x D049) + ((-1 : R)^2 * (value x A24) * (value x D037) + ((-1 : R)^3 * (value x A25) * (value x D021) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity053
theorem linear_identity053 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J053 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH053 x j * childD053 x j + entriesA053 x j * childJ053 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs053 linearChecked053
  simp only [linearPairs053, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J053 = ((-1 : R)^0 * ((value x H20) * (value x D052) + (value x A20) * (value x J052)) + ((-1 : R)^1 * ((value x H22) * (value x D049) + (value x A22) * (value x J049)) + ((-1 : R)^2 * ((value x H24) * (value x D037) + (value x A24) * (value x J037)) + ((-1 : R)^3 * ((value x H25) * (value x D021) + (value x A25) * (value x J021)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity053
def entriesA054 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A21
  | 1 => value x A22
  | 2 => value x A24
  | _ => value x A25
def entriesH054 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H21
  | 1 => value x H22
  | 2 => value x H24
  | _ => value x H25
def childD054 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D052
  | 1 => value x D050
  | 2 => value x D038
  | _ => value x D022
def childJ054 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J052
  | 1 => value x J050
  | 2 => value x J038
  | _ => value x J022
theorem const_identity054 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D054 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA054 x j * childD054 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs054 constChecked054
  simp only [constPairs054, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D054 = ((-1 : R)^0 * (value x A21) * (value x D052) + ((-1 : R)^1 * (value x A22) * (value x D050) + ((-1 : R)^2 * (value x A24) * (value x D038) + ((-1 : R)^3 * (value x A25) * (value x D022) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity054
theorem linear_identity054 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J054 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH054 x j * childD054 x j + entriesA054 x j * childJ054 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs054 linearChecked054
  simp only [linearPairs054, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J054 = ((-1 : R)^0 * ((value x H21) * (value x D052) + (value x A21) * (value x J052)) + ((-1 : R)^1 * ((value x H22) * (value x D050) + (value x A22) * (value x J050)) + ((-1 : R)^2 * ((value x H24) * (value x D038) + (value x A24) * (value x J038)) + ((-1 : R)^3 * ((value x H25) * (value x D022) + (value x A25) * (value x J022)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity054
def entriesA057 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A20
  | 1 => value x A23
  | 2 => value x A24
  | _ => value x A25
def entriesH057 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H20
  | 1 => value x H23
  | 2 => value x H24
  | _ => value x H25
def childD057 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D056
  | 1 => value x D049
  | 2 => value x D041
  | _ => value x D025
def childJ057 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J056
  | 1 => value x J049
  | 2 => value x J041
  | _ => value x J025
theorem const_identity057 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D057 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA057 x j * childD057 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs057 constChecked057
  simp only [constPairs057, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D057 = ((-1 : R)^0 * (value x A20) * (value x D056) + ((-1 : R)^1 * (value x A23) * (value x D049) + ((-1 : R)^2 * (value x A24) * (value x D041) + ((-1 : R)^3 * (value x A25) * (value x D025) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity057
theorem linear_identity057 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J057 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH057 x j * childD057 x j + entriesA057 x j * childJ057 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs057 linearChecked057
  simp only [linearPairs057, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J057 = ((-1 : R)^0 * ((value x H20) * (value x D056) + (value x A20) * (value x J056)) + ((-1 : R)^1 * ((value x H23) * (value x D049) + (value x A23) * (value x J049)) + ((-1 : R)^2 * ((value x H24) * (value x D041) + (value x A24) * (value x J041)) + ((-1 : R)^3 * ((value x H25) * (value x D025) + (value x A25) * (value x J025)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity057
def entriesA058 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A21
  | 1 => value x A23
  | 2 => value x A24
  | _ => value x A25
def entriesH058 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H21
  | 1 => value x H23
  | 2 => value x H24
  | _ => value x H25
def childD058 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D056
  | 1 => value x D050
  | 2 => value x D042
  | _ => value x D026
def childJ058 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J056
  | 1 => value x J050
  | 2 => value x J042
  | _ => value x J026
theorem const_identity058 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D058 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA058 x j * childD058 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs058 constChecked058
  simp only [constPairs058, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D058 = ((-1 : R)^0 * (value x A21) * (value x D056) + ((-1 : R)^1 * (value x A23) * (value x D050) + ((-1 : R)^2 * (value x A24) * (value x D042) + ((-1 : R)^3 * (value x A25) * (value x D026) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity058
theorem linear_identity058 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J058 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH058 x j * childD058 x j + entriesA058 x j * childJ058 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs058 linearChecked058
  simp only [linearPairs058, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J058 = ((-1 : R)^0 * ((value x H21) * (value x D056) + (value x A21) * (value x J056)) + ((-1 : R)^1 * ((value x H23) * (value x D050) + (value x A23) * (value x J050)) + ((-1 : R)^2 * ((value x H24) * (value x D042) + (value x A24) * (value x J042)) + ((-1 : R)^3 * ((value x H25) * (value x D026) + (value x A25) * (value x J026)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity058
def entriesA060 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A22
  | 1 => value x A23
  | 2 => value x A24
  | _ => value x A25
def entriesH060 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H22
  | 1 => value x H23
  | 2 => value x H24
  | _ => value x H25
def childD060 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D056
  | 1 => value x D052
  | 2 => value x D044
  | _ => value x D028
def childJ060 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J056
  | 1 => value x J052
  | 2 => value x J044
  | _ => value x J028
theorem const_identity060 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D060 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA060 x j * childD060 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs060 constChecked060
  simp only [constPairs060, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D060 = ((-1 : R)^0 * (value x A22) * (value x D056) + ((-1 : R)^1 * (value x A23) * (value x D052) + ((-1 : R)^2 * (value x A24) * (value x D044) + ((-1 : R)^3 * (value x A25) * (value x D028) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity060
theorem linear_identity060 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J060 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH060 x j * childD060 x j + entriesA060 x j * childJ060 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs060 linearChecked060
  simp only [linearPairs060, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J060 = ((-1 : R)^0 * ((value x H22) * (value x D056) + (value x A22) * (value x J056)) + ((-1 : R)^1 * ((value x H23) * (value x D052) + (value x A23) * (value x J052)) + ((-1 : R)^2 * ((value x H24) * (value x D044) + (value x A24) * (value x J044)) + ((-1 : R)^3 * ((value x H25) * (value x D028) + (value x A25) * (value x J028)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity060
end N6.ResultantMinors
