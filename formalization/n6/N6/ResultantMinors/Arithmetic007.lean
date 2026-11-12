import N6.ResultantMinors.ArithmeticHelpers
import N6.ResultantMinors.Ground007
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace N6.ResultantMinors
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
def entriesA031 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x A10
  | 1 => value x A11
  | 2 => value x A12
  | 3 => value x A13
  | _ => value x A14
def entriesH031 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x H10
  | 1 => value x H11
  | 2 => value x H12
  | 3 => value x H13
  | _ => value x H14
def childD031 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x D030
  | 1 => value x D029
  | 2 => value x D027
  | 3 => value x D023
  | _ => value x D015
def childJ031 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x J030
  | 1 => value x J029
  | 2 => value x J027
  | 3 => value x J023
  | _ => value x J015
theorem const_identity031 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D031 = ∑ j : Fin 5, (-1 : R)^j.val * entriesA031 x j * childD031 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs031 constChecked031
  simp only [constPairs031, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D031 = ((-1 : R)^0 * (value x A10) * (value x D030) + ((-1 : R)^1 * (value x A11) * (value x D029) + ((-1 : R)^2 * (value x A12) * (value x D027) + ((-1 : R)^3 * (value x A13) * (value x D023) + ((-1 : R)^4 * (value x A14) * (value x D015) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity031
theorem linear_identity031 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J031 = ∑ j : Fin 5, (-1 : R)^j.val * (entriesH031 x j * childD031 x j + entriesA031 x j * childJ031 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs031 linearChecked031
  simp only [linearPairs031, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J031 = ((-1 : R)^0 * ((value x H10) * (value x D030) + (value x A10) * (value x J030)) + ((-1 : R)^1 * ((value x H11) * (value x D029) + (value x A11) * (value x J029)) + ((-1 : R)^2 * ((value x H12) * (value x D027) + (value x A12) * (value x J027)) + ((-1 : R)^3 * ((value x H13) * (value x D023) + (value x A13) * (value x J023)) + ((-1 : R)^4 * ((value x H14) * (value x D015) + (value x A14) * (value x J015)) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity031
def entriesA047 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x A10
  | 1 => value x A11
  | 2 => value x A12
  | 3 => value x A13
  | _ => value x A15
def entriesH047 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x H10
  | 1 => value x H11
  | 2 => value x H12
  | 3 => value x H13
  | _ => value x H15
def childD047 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x D046
  | 1 => value x D045
  | 2 => value x D043
  | 3 => value x D039
  | _ => value x D015
def childJ047 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x J046
  | 1 => value x J045
  | 2 => value x J043
  | 3 => value x J039
  | _ => value x J015
theorem const_identity047 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D047 = ∑ j : Fin 5, (-1 : R)^j.val * entriesA047 x j * childD047 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs047 constChecked047
  simp only [constPairs047, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D047 = ((-1 : R)^0 * (value x A10) * (value x D046) + ((-1 : R)^1 * (value x A11) * (value x D045) + ((-1 : R)^2 * (value x A12) * (value x D043) + ((-1 : R)^3 * (value x A13) * (value x D039) + ((-1 : R)^4 * (value x A15) * (value x D015) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity047
theorem linear_identity047 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J047 = ∑ j : Fin 5, (-1 : R)^j.val * (entriesH047 x j * childD047 x j + entriesA047 x j * childJ047 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs047 linearChecked047
  simp only [linearPairs047, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J047 = ((-1 : R)^0 * ((value x H10) * (value x D046) + (value x A10) * (value x J046)) + ((-1 : R)^1 * ((value x H11) * (value x D045) + (value x A11) * (value x J045)) + ((-1 : R)^2 * ((value x H12) * (value x D043) + (value x A12) * (value x J043)) + ((-1 : R)^3 * ((value x H13) * (value x D039) + (value x A13) * (value x J039)) + ((-1 : R)^4 * ((value x H15) * (value x D015) + (value x A15) * (value x J015)) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity047
def entriesA055 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x A10
  | 1 => value x A11
  | 2 => value x A12
  | 3 => value x A14
  | _ => value x A15
def entriesH055 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x H10
  | 1 => value x H11
  | 2 => value x H12
  | 3 => value x H14
  | _ => value x H15
def childD055 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x D054
  | 1 => value x D053
  | 2 => value x D051
  | 3 => value x D039
  | _ => value x D023
def childJ055 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x J054
  | 1 => value x J053
  | 2 => value x J051
  | 3 => value x J039
  | _ => value x J023
theorem const_identity055 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D055 = ∑ j : Fin 5, (-1 : R)^j.val * entriesA055 x j * childD055 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs055 constChecked055
  simp only [constPairs055, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D055 = ((-1 : R)^0 * (value x A10) * (value x D054) + ((-1 : R)^1 * (value x A11) * (value x D053) + ((-1 : R)^2 * (value x A12) * (value x D051) + ((-1 : R)^3 * (value x A14) * (value x D039) + ((-1 : R)^4 * (value x A15) * (value x D023) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity055
theorem linear_identity055 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J055 = ∑ j : Fin 5, (-1 : R)^j.val * (entriesH055 x j * childD055 x j + entriesA055 x j * childJ055 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs055 linearChecked055
  simp only [linearPairs055, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J055 = ((-1 : R)^0 * ((value x H10) * (value x D054) + (value x A10) * (value x J054)) + ((-1 : R)^1 * ((value x H11) * (value x D053) + (value x A11) * (value x J053)) + ((-1 : R)^2 * ((value x H12) * (value x D051) + (value x A12) * (value x J051)) + ((-1 : R)^3 * ((value x H14) * (value x D039) + (value x A14) * (value x J039)) + ((-1 : R)^4 * ((value x H15) * (value x D023) + (value x A15) * (value x J023)) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity055
def entriesA059 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x A10
  | 1 => value x A11
  | 2 => value x A13
  | 3 => value x A14
  | _ => value x A15
def entriesH059 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x H10
  | 1 => value x H11
  | 2 => value x H13
  | 3 => value x H14
  | _ => value x H15
def childD059 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x D058
  | 1 => value x D057
  | 2 => value x D051
  | 3 => value x D043
  | _ => value x D027
def childJ059 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x J058
  | 1 => value x J057
  | 2 => value x J051
  | 3 => value x J043
  | _ => value x J027
theorem const_identity059 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D059 = ∑ j : Fin 5, (-1 : R)^j.val * entriesA059 x j * childD059 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs059 constChecked059
  simp only [constPairs059, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D059 = ((-1 : R)^0 * (value x A10) * (value x D058) + ((-1 : R)^1 * (value x A11) * (value x D057) + ((-1 : R)^2 * (value x A13) * (value x D051) + ((-1 : R)^3 * (value x A14) * (value x D043) + ((-1 : R)^4 * (value x A15) * (value x D027) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity059
theorem linear_identity059 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J059 = ∑ j : Fin 5, (-1 : R)^j.val * (entriesH059 x j * childD059 x j + entriesA059 x j * childJ059 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs059 linearChecked059
  simp only [linearPairs059, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J059 = ((-1 : R)^0 * ((value x H10) * (value x D058) + (value x A10) * (value x J058)) + ((-1 : R)^1 * ((value x H11) * (value x D057) + (value x A11) * (value x J057)) + ((-1 : R)^2 * ((value x H13) * (value x D051) + (value x A13) * (value x J051)) + ((-1 : R)^3 * ((value x H14) * (value x D043) + (value x A14) * (value x J043)) + ((-1 : R)^4 * ((value x H15) * (value x D027) + (value x A15) * (value x J027)) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity059
def entriesA061 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x A10
  | 1 => value x A12
  | 2 => value x A13
  | 3 => value x A14
  | _ => value x A15
def entriesH061 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x H10
  | 1 => value x H12
  | 2 => value x H13
  | 3 => value x H14
  | _ => value x H15
def childD061 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x D060
  | 1 => value x D057
  | 2 => value x D053
  | 3 => value x D045
  | _ => value x D029
def childJ061 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x J060
  | 1 => value x J057
  | 2 => value x J053
  | 3 => value x J045
  | _ => value x J029
theorem const_identity061 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D061 = ∑ j : Fin 5, (-1 : R)^j.val * entriesA061 x j * childD061 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs061 constChecked061
  simp only [constPairs061, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D061 = ((-1 : R)^0 * (value x A10) * (value x D060) + ((-1 : R)^1 * (value x A12) * (value x D057) + ((-1 : R)^2 * (value x A13) * (value x D053) + ((-1 : R)^3 * (value x A14) * (value x D045) + ((-1 : R)^4 * (value x A15) * (value x D029) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity061
theorem linear_identity061 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J061 = ∑ j : Fin 5, (-1 : R)^j.val * (entriesH061 x j * childD061 x j + entriesA061 x j * childJ061 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs061 linearChecked061
  simp only [linearPairs061, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J061 = ((-1 : R)^0 * ((value x H10) * (value x D060) + (value x A10) * (value x J060)) + ((-1 : R)^1 * ((value x H12) * (value x D057) + (value x A12) * (value x J057)) + ((-1 : R)^2 * ((value x H13) * (value x D053) + (value x A13) * (value x J053)) + ((-1 : R)^3 * ((value x H14) * (value x D045) + (value x A14) * (value x J045)) + ((-1 : R)^4 * ((value x H15) * (value x D029) + (value x A15) * (value x J029)) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity061
def entriesA062 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x A11
  | 1 => value x A12
  | 2 => value x A13
  | 3 => value x A14
  | _ => value x A15
def entriesH062 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x H11
  | 1 => value x H12
  | 2 => value x H13
  | 3 => value x H14
  | _ => value x H15
def childD062 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x D060
  | 1 => value x D058
  | 2 => value x D054
  | 3 => value x D046
  | _ => value x D030
def childJ062 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 5) : R :=
  match j.val with
  | 0 => value x J060
  | 1 => value x J058
  | 2 => value x J054
  | 3 => value x J046
  | _ => value x J030
theorem const_identity062 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D062 = ∑ j : Fin 5, (-1 : R)^j.val * entriesA062 x j * childD062 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs062 constChecked062
  simp only [constPairs062, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D062 = ((-1 : R)^0 * (value x A11) * (value x D060) + ((-1 : R)^1 * (value x A12) * (value x D058) + ((-1 : R)^2 * (value x A13) * (value x D054) + ((-1 : R)^3 * (value x A14) * (value x D046) + ((-1 : R)^4 * (value x A15) * (value x D030) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity062
theorem linear_identity062 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J062 = ∑ j : Fin 5, (-1 : R)^j.val * (entriesH062 x j * childD062 x j + entriesA062 x j * childJ062 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs062 linearChecked062
  simp only [linearPairs062, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J062 = ((-1 : R)^0 * ((value x H11) * (value x D060) + (value x A11) * (value x J060)) + ((-1 : R)^1 * ((value x H12) * (value x D058) + (value x A12) * (value x J058)) + ((-1 : R)^2 * ((value x H13) * (value x D054) + (value x A13) * (value x J054)) + ((-1 : R)^3 * ((value x H14) * (value x D046) + (value x A14) * (value x J046)) + ((-1 : R)^4 * ((value x H15) * (value x D030) + (value x A15) * (value x J030)) + (0 : R))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity062
def entriesA063 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 6) : R :=
  match j.val with
  | 0 => value x A00
  | 1 => value x A01
  | 2 => value x A02
  | 3 => value x A03
  | 4 => value x A04
  | _ => value x A05
def entriesH063 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 6) : R :=
  match j.val with
  | 0 => value x H00
  | 1 => value x H01
  | 2 => value x H02
  | 3 => value x H03
  | 4 => value x H04
  | _ => value x H05
def childD063 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 6) : R :=
  match j.val with
  | 0 => value x D062
  | 1 => value x D061
  | 2 => value x D059
  | 3 => value x D055
  | 4 => value x D047
  | _ => value x D031
def childJ063 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 6) : R :=
  match j.val with
  | 0 => value x J062
  | 1 => value x J061
  | 2 => value x J059
  | 3 => value x J055
  | 4 => value x J047
  | _ => value x J031
theorem const_identity063 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D063 = ∑ j : Fin 6, (-1 : R)^j.val * entriesA063 x j * childD063 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs063 constChecked063
  simp only [constPairs063, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D063 = ((-1 : R)^0 * (value x A00) * (value x D062) + ((-1 : R)^1 * (value x A01) * (value x D061) + ((-1 : R)^2 * (value x A02) * (value x D059) + ((-1 : R)^3 * (value x A03) * (value x D055) + ((-1 : R)^4 * (value x A04) * (value x D047) + ((-1 : R)^5 * (value x A05) * (value x D031) + (0 : R)))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity063
theorem linear_identity063 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J063 = ∑ j : Fin 6, (-1 : R)^j.val * (entriesH063 x j * childD063 x j + entriesA063 x j * childJ063 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs063 linearChecked063
  simp only [linearPairs063, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J063 = ((-1 : R)^0 * ((value x H00) * (value x D062) + (value x A00) * (value x J062)) + ((-1 : R)^1 * ((value x H01) * (value x D061) + (value x A01) * (value x J061)) + ((-1 : R)^2 * ((value x H02) * (value x D059) + (value x A02) * (value x J059)) + ((-1 : R)^3 * ((value x H03) * (value x D055) + (value x A03) * (value x J055)) + ((-1 : R)^4 * ((value x H04) * (value x D047) + (value x A04) * (value x J047)) + ((-1 : R)^5 * ((value x H05) * (value x D031) + (value x A05) * (value x J031)) + (0 : R)))))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity063
end N6.ResultantMinors
