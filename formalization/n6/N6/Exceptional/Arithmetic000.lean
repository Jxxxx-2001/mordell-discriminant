import N6.Exceptional.ArithmeticHelpers
import N6.Exceptional.Ground000
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
def entriesA001 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x A50
def entriesH001 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x H50
def childD001 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x D000
def childJ001 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x J000
theorem const_identity001 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D001 = ∑ j : Fin 1, (-1 : R)^j.val * entriesA001 x j * childD001 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs001 constChecked001
  simp only [constPairs001, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D001 = ((-1 : R)^0 * (value x A50) * (value x D000) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity001
theorem linear_identity001 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J001 = ∑ j : Fin 1, (-1 : R)^j.val * (entriesH001 x j * childD001 x j + entriesA001 x j * childJ001 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs001 linearChecked001
  simp only [linearPairs001, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J001 = ((-1 : R)^0 * ((value x H50) * (value x D000) + (value x A50) * (value x J000)) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity001
def entriesA002 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x A51
def entriesH002 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x H51
def childD002 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x D000
def childJ002 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x J000
theorem const_identity002 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D002 = ∑ j : Fin 1, (-1 : R)^j.val * entriesA002 x j * childD002 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs002 constChecked002
  simp only [constPairs002, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D002 = ((-1 : R)^0 * (value x A51) * (value x D000) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity002
theorem linear_identity002 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J002 = ∑ j : Fin 1, (-1 : R)^j.val * (entriesH002 x j * childD002 x j + entriesA002 x j * childJ002 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs002 linearChecked002
  simp only [linearPairs002, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J002 = ((-1 : R)^0 * ((value x H51) * (value x D000) + (value x A51) * (value x J000)) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity002
def entriesA004 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x A52
def entriesH004 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x H52
def childD004 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x D000
def childJ004 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x J000
theorem const_identity004 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D004 = ∑ j : Fin 1, (-1 : R)^j.val * entriesA004 x j * childD004 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs004 constChecked004
  simp only [constPairs004, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D004 = ((-1 : R)^0 * (value x A52) * (value x D000) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity004
theorem linear_identity004 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J004 = ∑ j : Fin 1, (-1 : R)^j.val * (entriesH004 x j * childD004 x j + entriesA004 x j * childJ004 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs004 linearChecked004
  simp only [linearPairs004, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J004 = ((-1 : R)^0 * ((value x H52) * (value x D000) + (value x A52) * (value x J000)) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity004
def entriesA008 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x A53
def entriesH008 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x H53
def childD008 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x D000
def childJ008 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x J000
theorem const_identity008 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D008 = ∑ j : Fin 1, (-1 : R)^j.val * entriesA008 x j * childD008 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs008 constChecked008
  simp only [constPairs008, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D008 = ((-1 : R)^0 * (value x A53) * (value x D000) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity008
theorem linear_identity008 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J008 = ∑ j : Fin 1, (-1 : R)^j.val * (entriesH008 x j * childD008 x j + entriesA008 x j * childJ008 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs008 linearChecked008
  simp only [linearPairs008, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J008 = ((-1 : R)^0 * ((value x H53) * (value x D000) + (value x A53) * (value x J000)) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity008
def entriesA016 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x A54
def entriesH016 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x H54
def childD016 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x D000
def childJ016 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x J000
theorem const_identity016 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D016 = ∑ j : Fin 1, (-1 : R)^j.val * entriesA016 x j * childD016 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs016 constChecked016
  simp only [constPairs016, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D016 = ((-1 : R)^0 * (value x A54) * (value x D000) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity016
theorem linear_identity016 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J016 = ∑ j : Fin 1, (-1 : R)^j.val * (entriesH016 x j * childD016 x j + entriesA016 x j * childJ016 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs016 linearChecked016
  simp only [linearPairs016, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J016 = ((-1 : R)^0 * ((value x H54) * (value x D000) + (value x A54) * (value x J000)) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity016
def entriesA032 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x A55
def entriesH032 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x H55
def childD032 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x D000
def childJ032 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 1) : R :=
  match j.val with
  | _ => value x J000
theorem const_identity032 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D032 = ∑ j : Fin 1, (-1 : R)^j.val * entriesA032 x j * childD032 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs032 constChecked032
  simp only [constPairs032, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D032 = ((-1 : R)^0 * (value x A55) * (value x D000) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity032
theorem linear_identity032 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J032 = ∑ j : Fin 1, (-1 : R)^j.val * (entriesH032 x j * childD032 x j + entriesA032 x j * childJ032 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs032 linearChecked032
  simp only [linearPairs032, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J032 = ((-1 : R)^0 * ((value x H55) * (value x D000) + (value x A55) * (value x J000)) + (0 : R))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity032
def entriesA003 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A40
  | _ => value x A41
def entriesH003 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H40
  | _ => value x H41
def childD003 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D002
  | _ => value x D001
def childJ003 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J002
  | _ => value x J001
theorem const_identity003 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D003 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA003 x j * childD003 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs003 constChecked003
  simp only [constPairs003, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D003 = ((-1 : R)^0 * (value x A40) * (value x D002) + ((-1 : R)^1 * (value x A41) * (value x D001) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity003
theorem linear_identity003 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J003 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH003 x j * childD003 x j + entriesA003 x j * childJ003 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs003 linearChecked003
  simp only [linearPairs003, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J003 = ((-1 : R)^0 * ((value x H40) * (value x D002) + (value x A40) * (value x J002)) + ((-1 : R)^1 * ((value x H41) * (value x D001) + (value x A41) * (value x J001)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity003
def entriesA005 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A40
  | _ => value x A42
def entriesH005 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H40
  | _ => value x H42
def childD005 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D004
  | _ => value x D001
def childJ005 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J004
  | _ => value x J001
theorem const_identity005 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D005 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA005 x j * childD005 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs005 constChecked005
  simp only [constPairs005, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D005 = ((-1 : R)^0 * (value x A40) * (value x D004) + ((-1 : R)^1 * (value x A42) * (value x D001) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity005
theorem linear_identity005 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J005 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH005 x j * childD005 x j + entriesA005 x j * childJ005 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs005 linearChecked005
  simp only [linearPairs005, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J005 = ((-1 : R)^0 * ((value x H40) * (value x D004) + (value x A40) * (value x J004)) + ((-1 : R)^1 * ((value x H42) * (value x D001) + (value x A42) * (value x J001)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity005
end N6.Exceptional
