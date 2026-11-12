import review.SparseCheck
import review.Dcolon1Data
import N6.Chart

set_option maxRecDepth 32000
set_option maxHeartbeats 3000000

namespace N6.Dcolon1
open N6.SparseCheck

variable {K : Type*} [Field K] [CharZero K]

theorem chartF0 (x : Fin 5 → K) :
    value x f0Data = N6.Chart.F0 (x 4) (x 3) (x 2) (x 1) := by
  simp [f0Data, value_append, f0DataPart0, f0DataPart1, f0DataPart2, f0DataPart3, f0DataPart4, value, monVal, N6.Chart.F0] <;> ring

theorem chartF1 (x : Fin 5 → K) :
    value x f1Data = N6.Chart.F1 (x 4) (x 3) (x 2) (x 1) := by
  simp [f1Data, value_append, f1DataPart0, f1DataPart1, f1DataPart2, f1DataPart3, f1DataPart4, value, monVal, N6.Chart.F1] <;> ring

theorem chartF2 (x : Fin 5 → K) :
    value x f2Data = N6.Chart.F2 (x 4) (x 3) (x 2) (x 1) := by
  simp [f2Data, value_append, f2DataPart0, f2DataPart1, f2DataPart2, f2DataPart3, f2DataPart4, value, monVal, N6.Chart.F2] <;> ring

theorem chartF3 (x : Fin 5 → K) :
    value x f3Data = N6.Chart.F3 (x 4) (x 3) (x 2) (x 1) := by
  simp [f3Data, value_append, f3DataPart0, f3DataPart1, f3DataPart2, f3DataPart3, f3DataPart4, value, monVal, N6.Chart.F3] <;> ring

theorem chartD (x : Fin 5 → K) :
    value x dData = N6.Chart.D (x 4) (x 3) (x 2) (x 1) := by
  simp [dData, value_append, dDataPart0, dDataPart1, dDataPart2, dDataPart3, dDataPart4, value, monVal, N6.Chart.D] <;> ring


end N6.Dcolon1
