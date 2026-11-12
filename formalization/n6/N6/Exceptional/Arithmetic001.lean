import N6.Exceptional.ArithmeticHelpers
import N6.Exceptional.Ground001
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
def entriesA006 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A41
  | _ => value x A42
def entriesH006 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H41
  | _ => value x H42
def childD006 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D004
  | _ => value x D002
def childJ006 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J004
  | _ => value x J002
theorem const_identity006 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D006 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA006 x j * childD006 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs006 constChecked006
  simp only [constPairs006, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D006 = ((-1 : R)^0 * (value x A41) * (value x D004) + ((-1 : R)^1 * (value x A42) * (value x D002) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity006
theorem linear_identity006 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J006 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH006 x j * childD006 x j + entriesA006 x j * childJ006 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs006 linearChecked006
  simp only [linearPairs006, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J006 = ((-1 : R)^0 * ((value x H41) * (value x D004) + (value x A41) * (value x J004)) + ((-1 : R)^1 * ((value x H42) * (value x D002) + (value x A42) * (value x J002)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity006
def entriesA009 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A40
  | _ => value x A43
def entriesH009 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H40
  | _ => value x H43
def childD009 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D008
  | _ => value x D001
def childJ009 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J008
  | _ => value x J001
theorem const_identity009 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D009 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA009 x j * childD009 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs009 constChecked009
  simp only [constPairs009, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D009 = ((-1 : R)^0 * (value x A40) * (value x D008) + ((-1 : R)^1 * (value x A43) * (value x D001) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity009
theorem linear_identity009 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J009 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH009 x j * childD009 x j + entriesA009 x j * childJ009 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs009 linearChecked009
  simp only [linearPairs009, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J009 = ((-1 : R)^0 * ((value x H40) * (value x D008) + (value x A40) * (value x J008)) + ((-1 : R)^1 * ((value x H43) * (value x D001) + (value x A43) * (value x J001)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity009
def entriesA010 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A41
  | _ => value x A43
def entriesH010 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H41
  | _ => value x H43
def childD010 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D008
  | _ => value x D002
def childJ010 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J008
  | _ => value x J002
theorem const_identity010 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D010 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA010 x j * childD010 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs010 constChecked010
  simp only [constPairs010, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D010 = ((-1 : R)^0 * (value x A41) * (value x D008) + ((-1 : R)^1 * (value x A43) * (value x D002) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity010
theorem linear_identity010 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J010 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH010 x j * childD010 x j + entriesA010 x j * childJ010 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs010 linearChecked010
  simp only [linearPairs010, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J010 = ((-1 : R)^0 * ((value x H41) * (value x D008) + (value x A41) * (value x J008)) + ((-1 : R)^1 * ((value x H43) * (value x D002) + (value x A43) * (value x J002)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity010
def entriesA012 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A42
  | _ => value x A43
def entriesH012 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H42
  | _ => value x H43
def childD012 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D008
  | _ => value x D004
def childJ012 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J008
  | _ => value x J004
theorem const_identity012 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D012 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA012 x j * childD012 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs012 constChecked012
  simp only [constPairs012, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D012 = ((-1 : R)^0 * (value x A42) * (value x D008) + ((-1 : R)^1 * (value x A43) * (value x D004) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity012
theorem linear_identity012 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J012 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH012 x j * childD012 x j + entriesA012 x j * childJ012 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs012 linearChecked012
  simp only [linearPairs012, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J012 = ((-1 : R)^0 * ((value x H42) * (value x D008) + (value x A42) * (value x J008)) + ((-1 : R)^1 * ((value x H43) * (value x D004) + (value x A43) * (value x J004)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity012
def entriesA017 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A40
  | _ => value x A44
def entriesH017 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H40
  | _ => value x H44
def childD017 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D016
  | _ => value x D001
def childJ017 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J016
  | _ => value x J001
theorem const_identity017 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D017 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA017 x j * childD017 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs017 constChecked017
  simp only [constPairs017, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D017 = ((-1 : R)^0 * (value x A40) * (value x D016) + ((-1 : R)^1 * (value x A44) * (value x D001) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity017
theorem linear_identity017 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J017 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH017 x j * childD017 x j + entriesA017 x j * childJ017 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs017 linearChecked017
  simp only [linearPairs017, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J017 = ((-1 : R)^0 * ((value x H40) * (value x D016) + (value x A40) * (value x J016)) + ((-1 : R)^1 * ((value x H44) * (value x D001) + (value x A44) * (value x J001)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity017
def entriesA018 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A41
  | _ => value x A44
def entriesH018 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H41
  | _ => value x H44
def childD018 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D016
  | _ => value x D002
def childJ018 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J016
  | _ => value x J002
theorem const_identity018 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D018 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA018 x j * childD018 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs018 constChecked018
  simp only [constPairs018, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D018 = ((-1 : R)^0 * (value x A41) * (value x D016) + ((-1 : R)^1 * (value x A44) * (value x D002) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity018
theorem linear_identity018 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J018 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH018 x j * childD018 x j + entriesA018 x j * childJ018 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs018 linearChecked018
  simp only [linearPairs018, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J018 = ((-1 : R)^0 * ((value x H41) * (value x D016) + (value x A41) * (value x J016)) + ((-1 : R)^1 * ((value x H44) * (value x D002) + (value x A44) * (value x J002)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity018
def entriesA020 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A42
  | _ => value x A44
def entriesH020 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H42
  | _ => value x H44
def childD020 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D016
  | _ => value x D004
def childJ020 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J016
  | _ => value x J004
theorem const_identity020 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D020 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA020 x j * childD020 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs020 constChecked020
  simp only [constPairs020, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D020 = ((-1 : R)^0 * (value x A42) * (value x D016) + ((-1 : R)^1 * (value x A44) * (value x D004) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity020
theorem linear_identity020 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J020 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH020 x j * childD020 x j + entriesA020 x j * childJ020 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs020 linearChecked020
  simp only [linearPairs020, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J020 = ((-1 : R)^0 * ((value x H42) * (value x D016) + (value x A42) * (value x J016)) + ((-1 : R)^1 * ((value x H44) * (value x D004) + (value x A44) * (value x J004)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity020
def entriesA024 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x A43
  | _ => value x A44
def entriesH024 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x H43
  | _ => value x H44
def childD024 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x D016
  | _ => value x D008
def childJ024 {R : Type*} [CommRing R] (x : Fin 5 → R) (j : Fin 2) : R :=
  match j.val with
  | 0 => value x J016
  | _ => value x J008
theorem const_identity024 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x D024 = ∑ j : Fin 2, (-1 : R)^j.val * entriesA024 x j * childD024 x j := by
  have h := N6.SparseProductReduce.pairs_vanish x constPairs024 constChecked024
  simp only [constPairs024, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x D024 = ((-1 : R)^0 * (value x A43) * (value x D016) + ((-1 : R)^1 * (value x A44) * (value x D008) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms const_identity024
theorem linear_identity024 {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x J024 = ∑ j : Fin 2, (-1 : R)^j.val * (entriesH024 x j * childD024 x j + entriesA024 x j * childJ024 x j) := by
  have h := N6.SparseProductReduce.pairs_vanish x linearPairs024 linearChecked024
  simp only [linearPairs024, pairs, value_scaled, value_one, value_D000, Int.cast_one, Int.cast_neg, mul_one, add_zero] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change value x J024 = ((-1 : R)^0 * ((value x H43) * (value x D016) + (value x A43) * (value x J016)) + ((-1 : R)^1 * ((value x H44) * (value x D008) + (value x A44) * (value x J008)) + (0 : R)))
  try simp only [value_one, value_D000]
  all_goals linear_combination -h
#print axioms linear_identity024
end N6.Exceptional
