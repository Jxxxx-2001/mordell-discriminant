import N6.ResultantMinors.RawCoefficientGround
import N6.ResultantMinors.ArithmeticHelpers
import N6.ResultantMinors.Bindings
import N6.Chart
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
namespace N6.ResultantMinors
open N6.SparseCheck
theorem actualD_value {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x actualDData = value x rawDData := by
  have h := N6.SparseCheck.value_zero x rawDChecked
  change value x (merge actualDData (scaled (-1) rawDData)) = 0 at h
  rw [value_merge, value_scaled] at h
  have hn : value x actualDData = value x rawDData := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, sub_eq_add_neg] using h
  exact hn
theorem rawD_chart {K : Type*} [Field K] [CharZero K] (b c d e : K) :
    value (point b c d e (0 : K)) rawDData = N6.Chart.originalD b c d e := by
  simp only [rawDData, rawDDataPart0, rawDDataPart1, rawDDataPart2, rawDDataPart3, rawDDataPart4, value_append, value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, N6.Chart.originalD]
  ring
theorem actualD_chart {K : Type*} [Field K] [CharZero K] (b c d e : K) :
    value (point b c d e (0 : K)) actualDData = N6.Chart.originalD b c d e :=
  (actualD_value (point b c d e (0 : K))).trans (rawD_chart b c d e)
#print axioms actualD_value
#print axioms rawD_chart
#print axioms actualD_chart
theorem actualE0_value {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x actualE0Data = value x rawE0Data := by
  have h := N6.SparseCheck.value_zero x rawE0Checked
  change value x (merge actualE0Data (scaled (-1) rawE0Data)) = 0 at h
  rw [value_merge, value_scaled] at h
  have hn : value x actualE0Data = value x rawE0Data := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, sub_eq_add_neg] using h
  exact hn
theorem rawE0_chart {K : Type*} [Field K] [CharZero K] (b c d e : K) :
    value (point b c d e (0 : K)) rawE0Data = N6.Chart.E0 b c d e := by
  simp only [rawE0Data, rawE0DataPart0, rawE0DataPart1, rawE0DataPart2, rawE0DataPart3, rawE0DataPart4, value_append, value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, N6.Chart.E0]
  ring
theorem actualE0_chart {K : Type*} [Field K] [CharZero K] (b c d e : K) :
    value (point b c d e (0 : K)) actualE0Data = N6.Chart.E0 b c d e :=
  (actualE0_value (point b c d e (0 : K))).trans (rawE0_chart b c d e)
#print axioms actualE0_value
#print axioms rawE0_chart
#print axioms actualE0_chart
theorem actualE1_value {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x actualE1Data = value x rawE1Data := by
  have h := N6.SparseCheck.value_zero x rawE1Checked
  change value x (merge normalizedE1Data (scaled (-1) rawE1Data)) = 0 at h
  rw [value_merge, value_scaled] at h
  have hn : value x normalizedE1Data = value x rawE1Data := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, sub_eq_add_neg] using h
  simpa only [actualE1Data, normalizedE1Data, value_append, value_merge] using hn
theorem rawE1_chart {K : Type*} [Field K] [CharZero K] (b c d e : K) :
    value (point b c d e (0 : K)) rawE1Data = N6.Chart.E1 b c d e := by
  simp only [rawE1Data, rawE1DataPart0, rawE1DataPart1, rawE1DataPart2, rawE1DataPart3, rawE1DataPart4, value_append, value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, N6.Chart.E1]
  ring
theorem actualE1_chart {K : Type*} [Field K] [CharZero K] (b c d e : K) :
    value (point b c d e (0 : K)) actualE1Data = N6.Chart.E1 b c d e :=
  (actualE1_value (point b c d e (0 : K))).trans (rawE1_chart b c d e)
#print axioms actualE1_value
#print axioms rawE1_chart
#print axioms actualE1_chart
theorem actualE2_value {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x actualE2Data = value x rawE2Data := by
  have h := N6.SparseCheck.value_zero x rawE2Checked
  change value x (merge normalizedE2Data (scaled (-1) rawE2Data)) = 0 at h
  rw [value_merge, value_scaled] at h
  have hn : value x normalizedE2Data = value x rawE2Data := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, sub_eq_add_neg] using h
  simpa only [actualE2Data, normalizedE2Data, value_append, value_merge] using hn
theorem rawE2_chart {K : Type*} [Field K] [CharZero K] (b c d e : K) :
    value (point b c d e (0 : K)) rawE2Data = N6.Chart.E2 b c d e := by
  simp only [rawE2Data, rawE2DataPart0, rawE2DataPart1, rawE2DataPart2, rawE2DataPart3, rawE2DataPart4, value_append, value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, N6.Chart.E2]
  ring
theorem actualE2_chart {K : Type*} [Field K] [CharZero K] (b c d e : K) :
    value (point b c d e (0 : K)) actualE2Data = N6.Chart.E2 b c d e :=
  (actualE2_value (point b c d e (0 : K))).trans (rawE2_chart b c d e)
#print axioms actualE2_value
#print axioms rawE2_chart
#print axioms actualE2_chart
theorem actualE3_value {R : Type*} [CommRing R] (x : Fin 5 → R) :
    value x actualE3Data = value x rawE3Data := by
  have h := N6.SparseCheck.value_zero x rawE3Checked
  change value x (merge normalizedE3Data (scaled (-1) rawE3Data)) = 0 at h
  rw [value_merge, value_scaled] at h
  have hn : value x normalizedE3Data = value x rawE3Data := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, sub_eq_add_neg] using h
  simpa only [actualE3Data, normalizedE3Data, value_append, value_merge] using hn
theorem rawE3_chart {K : Type*} [Field K] [CharZero K] (b c d e : K) :
    value (point b c d e (0 : K)) rawE3Data = N6.Chart.E3 b c d e := by
  simp only [rawE3Data, rawE3DataPart0, rawE3DataPart1, rawE3DataPart2, rawE3DataPart3, rawE3DataPart4, value_append, value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, N6.Chart.E3]
  ring
theorem actualE3_chart {K : Type*} [Field K] [CharZero K] (b c d e : K) :
    value (point b c d e (0 : K)) actualE3Data = N6.Chart.E3 b c d e :=
  (actualE3_value (point b c d e (0 : K))).trans (rawE3_chart b c d e)
#print axioms actualE3_value
#print axioms rawE3_chart
#print axioms actualE3_chart
end N6.ResultantMinors
