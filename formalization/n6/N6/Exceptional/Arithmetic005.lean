import N6.Exceptional.ArithmeticHelpers
import N6.Exceptional.Ground005
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
def entriesA056 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x A33
  | 1 => value x A34
  | _ => value x A35
def entriesH056 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x H33
  | 1 => value x H34
  | _ => value x H35
def childD056 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x D048
  | 1 => value x D040
  | _ => value x D024
def childJ056 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 3) : R :=
  match j.val with
  | 0 => value x J048
  | 1 => value x J040
  | _ => value x J024
theorem const_identity056 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D056 = ∑ j : Fin 3, (-1 : R)^j.val * entriesA056 x j * childD056 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs056 constChecked056
  simp only [constPairs056, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D056 = ((-1 : R)^0 * (value x A33) * (value x D048) + ((-1 : R)^1 * (value x A34) * (value x D040) + ((-1 : R)^2 * (value x A35) * (value x D024) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity056
theorem linear_identity056 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J056 = ∑ j : Fin 3, (-1 : R)^j.val * (entriesH056 x j * childD056 x j + entriesA056 x j * childJ056 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs056 linearChecked056
  simp only [linearPairs056, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J056 = ((-1 : R)^0 * ((value x H33) * (value x D048) + (value x A33) * (value x J048)) + ((-1 : R)^1 * ((value x H34) * (value x D040) + (value x A34) * (value x J040)) + ((-1 : R)^2 * ((value x H35) * (value x D024) + (value x A35) * (value x J024)) + (0 : R))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity056
def entriesA015 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A20
  | 1 => value x A21
  | 2 => value x A22
  | _ => value x A23
def entriesH015 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H20
  | 1 => value x H21
  | 2 => value x H22
  | _ => value x H23
def childD015 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D014
  | 1 => value x D013
  | 2 => value x D011
  | _ => value x D007
def childJ015 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J014
  | 1 => value x J013
  | 2 => value x J011
  | _ => value x J007
theorem const_identity015 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D015 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA015 x j * childD015 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs015 constChecked015
  simp only [constPairs015, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D015 = ((-1 : R)^0 * (value x A20) * (value x D014) + ((-1 : R)^1 * (value x A21) * (value x D013) + ((-1 : R)^2 * (value x A22) * (value x D011) + ((-1 : R)^3 * (value x A23) * (value x D007) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity015
theorem linear_identity015 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J015 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH015 x j * childD015 x j + entriesA015 x j * childJ015 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs015 linearChecked015
  simp only [linearPairs015, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J015 = ((-1 : R)^0 * ((value x H20) * (value x D014) + (value x A20) * (value x J014)) + ((-1 : R)^1 * ((value x H21) * (value x D013) + (value x A21) * (value x J013)) + ((-1 : R)^2 * ((value x H22) * (value x D011) + (value x A22) * (value x J011)) + ((-1 : R)^3 * ((value x H23) * (value x D007) + (value x A23) * (value x J007)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity015
def entriesA023 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A20
  | 1 => value x A21
  | 2 => value x A22
  | _ => value x A24
def entriesH023 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H20
  | 1 => value x H21
  | 2 => value x H22
  | _ => value x H24
def childD023 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D022
  | 1 => value x D021
  | 2 => value x D019
  | _ => value x D007
def childJ023 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J022
  | 1 => value x J021
  | 2 => value x J019
  | _ => value x J007
theorem const_identity023 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D023 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA023 x j * childD023 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs023 constChecked023
  simp only [constPairs023, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D023 = ((-1 : R)^0 * (value x A20) * (value x D022) + ((-1 : R)^1 * (value x A21) * (value x D021) + ((-1 : R)^2 * (value x A22) * (value x D019) + ((-1 : R)^3 * (value x A24) * (value x D007) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity023
theorem linear_identity023 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J023 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH023 x j * childD023 x j + entriesA023 x j * childJ023 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs023 linearChecked023
  simp only [linearPairs023, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J023 = ((-1 : R)^0 * ((value x H20) * (value x D022) + (value x A20) * (value x J022)) + ((-1 : R)^1 * ((value x H21) * (value x D021) + (value x A21) * (value x J021)) + ((-1 : R)^2 * ((value x H22) * (value x D019) + (value x A22) * (value x J019)) + ((-1 : R)^3 * ((value x H24) * (value x D007) + (value x A24) * (value x J007)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity023
def entriesA027 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A20
  | 1 => value x A21
  | 2 => value x A23
  | _ => value x A24
def entriesH027 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H20
  | 1 => value x H21
  | 2 => value x H23
  | _ => value x H24
def childD027 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D026
  | 1 => value x D025
  | 2 => value x D019
  | _ => value x D011
def childJ027 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J026
  | 1 => value x J025
  | 2 => value x J019
  | _ => value x J011
theorem const_identity027 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D027 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA027 x j * childD027 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs027 constChecked027
  simp only [constPairs027, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D027 = ((-1 : R)^0 * (value x A20) * (value x D026) + ((-1 : R)^1 * (value x A21) * (value x D025) + ((-1 : R)^2 * (value x A23) * (value x D019) + ((-1 : R)^3 * (value x A24) * (value x D011) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity027
theorem linear_identity027 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J027 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH027 x j * childD027 x j + entriesA027 x j * childJ027 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs027 linearChecked027
  simp only [linearPairs027, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J027 = ((-1 : R)^0 * ((value x H20) * (value x D026) + (value x A20) * (value x J026)) + ((-1 : R)^1 * ((value x H21) * (value x D025) + (value x A21) * (value x J025)) + ((-1 : R)^2 * ((value x H23) * (value x D019) + (value x A23) * (value x J019)) + ((-1 : R)^3 * ((value x H24) * (value x D011) + (value x A24) * (value x J011)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity027
def entriesA029 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A20
  | 1 => value x A22
  | 2 => value x A23
  | _ => value x A24
def entriesH029 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H20
  | 1 => value x H22
  | 2 => value x H23
  | _ => value x H24
def childD029 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D028
  | 1 => value x D025
  | 2 => value x D021
  | _ => value x D013
def childJ029 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J028
  | 1 => value x J025
  | 2 => value x J021
  | _ => value x J013
theorem const_identity029 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D029 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA029 x j * childD029 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs029 constChecked029
  simp only [constPairs029, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D029 = ((-1 : R)^0 * (value x A20) * (value x D028) + ((-1 : R)^1 * (value x A22) * (value x D025) + ((-1 : R)^2 * (value x A23) * (value x D021) + ((-1 : R)^3 * (value x A24) * (value x D013) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity029
theorem linear_identity029 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J029 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH029 x j * childD029 x j + entriesA029 x j * childJ029 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs029 linearChecked029
  simp only [linearPairs029, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J029 = ((-1 : R)^0 * ((value x H20) * (value x D028) + (value x A20) * (value x J028)) + ((-1 : R)^1 * ((value x H22) * (value x D025) + (value x A22) * (value x J025)) + ((-1 : R)^2 * ((value x H23) * (value x D021) + (value x A23) * (value x J021)) + ((-1 : R)^3 * ((value x H24) * (value x D013) + (value x A24) * (value x J013)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity029
def entriesA030 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A21
  | 1 => value x A22
  | 2 => value x A23
  | _ => value x A24
def entriesH030 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H21
  | 1 => value x H22
  | 2 => value x H23
  | _ => value x H24
def childD030 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D028
  | 1 => value x D026
  | 2 => value x D022
  | _ => value x D014
def childJ030 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J028
  | 1 => value x J026
  | 2 => value x J022
  | _ => value x J014
theorem const_identity030 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D030 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA030 x j * childD030 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs030 constChecked030
  simp only [constPairs030, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D030 = ((-1 : R)^0 * (value x A21) * (value x D028) + ((-1 : R)^1 * (value x A22) * (value x D026) + ((-1 : R)^2 * (value x A23) * (value x D022) + ((-1 : R)^3 * (value x A24) * (value x D014) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity030
theorem linear_identity030 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J030 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH030 x j * childD030 x j + entriesA030 x j * childJ030 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs030 linearChecked030
  simp only [linearPairs030, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J030 = ((-1 : R)^0 * ((value x H21) * (value x D028) + (value x A21) * (value x J028)) + ((-1 : R)^1 * ((value x H22) * (value x D026) + (value x A22) * (value x J026)) + ((-1 : R)^2 * ((value x H23) * (value x D022) + (value x A23) * (value x J022)) + ((-1 : R)^3 * ((value x H24) * (value x D014) + (value x A24) * (value x J014)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity030
def entriesA039 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A20
  | 1 => value x A21
  | 2 => value x A22
  | _ => value x A25
def entriesH039 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H20
  | 1 => value x H21
  | 2 => value x H22
  | _ => value x H25
def childD039 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D038
  | 1 => value x D037
  | 2 => value x D035
  | _ => value x D007
def childJ039 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J038
  | 1 => value x J037
  | 2 => value x J035
  | _ => value x J007
theorem const_identity039 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D039 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA039 x j * childD039 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs039 constChecked039
  simp only [constPairs039, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D039 = ((-1 : R)^0 * (value x A20) * (value x D038) + ((-1 : R)^1 * (value x A21) * (value x D037) + ((-1 : R)^2 * (value x A22) * (value x D035) + ((-1 : R)^3 * (value x A25) * (value x D007) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity039
theorem linear_identity039 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J039 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH039 x j * childD039 x j + entriesA039 x j * childJ039 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs039 linearChecked039
  simp only [linearPairs039, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J039 = ((-1 : R)^0 * ((value x H20) * (value x D038) + (value x A20) * (value x J038)) + ((-1 : R)^1 * ((value x H21) * (value x D037) + (value x A21) * (value x J037)) + ((-1 : R)^2 * ((value x H22) * (value x D035) + (value x A22) * (value x J035)) + ((-1 : R)^3 * ((value x H25) * (value x D007) + (value x A25) * (value x J007)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity039
def entriesA043 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x A20
  | 1 => value x A21
  | 2 => value x A23
  | _ => value x A25
def entriesH043 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x H20
  | 1 => value x H21
  | 2 => value x H23
  | _ => value x H25
def childD043 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x D042
  | 1 => value x D041
  | 2 => value x D035
  | _ => value x D011
def childJ043 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 4) : R :=
  match j.val with
  | 0 => value x J042
  | 1 => value x J041
  | 2 => value x J035
  | _ => value x J011
theorem const_identity043 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D043 = ∑ j : Fin 4, (-1 : R)^j.val * entriesA043 x j * childD043 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs043 constChecked043
  simp only [constPairs043, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D043 = ((-1 : R)^0 * (value x A20) * (value x D042) + ((-1 : R)^1 * (value x A21) * (value x D041) + ((-1 : R)^2 * (value x A23) * (value x D035) + ((-1 : R)^3 * (value x A25) * (value x D011) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity043
theorem linear_identity043 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J043 = ∑ j : Fin 4, (-1 : R)^j.val * (entriesH043 x j * childD043 x j + entriesA043 x j * childJ043 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs043 linearChecked043
  simp only [linearPairs043, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J043 = ((-1 : R)^0 * ((value x H20) * (value x D042) + (value x A20) * (value x J042)) + ((-1 : R)^1 * ((value x H21) * (value x D041) + (value x A21) * (value x J041)) + ((-1 : R)^2 * ((value x H23) * (value x D035) + (value x A23) * (value x J035)) + ((-1 : R)^3 * ((value x H25) * (value x D011) + (value x A25) * (value x J011)) + (0 : R)))))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity043
end N6.Exceptional
