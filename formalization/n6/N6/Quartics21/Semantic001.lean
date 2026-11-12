import N6.Quartics21.Ground008
import N6.Quartics21.Ground009
import N6.Quartics21.Ground010
import N6.Quartics21.Ground011
import N6.Quartics21.Ground012
import N6.Quartics21.Ground013
import N6.Quartics21.Ground014
import review.KroneckerCheck
import review.KroneckerFastPack
import review.Dcolon1Chart
import N6.Saturation
import N6.Certificate
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000

namespace N6.Quartics21.Case008
open N6.SparseCheck N6.KroneckerCheck
theorem packed_ok : pairs (pack rad width) factorPairs = 0 :=
  (N6.KroneckerFastPack.pairs_fastPack_eq rad width 16 factorPairs).symm.trans fast_ok
theorem payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) factorPairs = 0 :=
  N6.KroneckerCheck.check x rad width factorPairs room_ok mass_ok packed_ok
theorem generic_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0) : value x gData = 0 := by
  have h := payload x
  simp only [factorPairs, pairs, h0, h1, h2, h3, mul_zero, add_zero, zero_add, scaledD, value_mapMul] at h
  apply N6.Saturation.cancel_D (x 0) (x 4) (value x N6.Dcolon1.dData) _ hs
  apply N6.Certificate.int_scaled_zero 403896000388258981335021178487400 (by decide)
  simpa [scalarTerm, monVal, mul_assoc] using h
theorem chart_vanish {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (h0 : N6.Chart.F0 (x 4) (x 3) (x 2) (x 1) = 0)
    (h1 : N6.Chart.F1 (x 4) (x 3) (x 2) (x 1) = 0)
    (h2 : N6.Chart.F2 (x 4) (x 3) (x 2) (x 1) = 0)
    (h3 : N6.Chart.F3 (x 4) (x 3) (x 2) (x 1) = 0)
    (hs : x 0 * x 4 * N6.Chart.D (x 4) (x 3) (x 2) (x 1) - 1 = 0) : value x gData = 0 := by
  apply generic_vanish x
  · simpa only [N6.Dcolon1.chartF0] using h0
  · simpa only [N6.Dcolon1.chartF1] using h1
  · simpa only [N6.Dcolon1.chartF2] using h2
  · simpa only [N6.Dcolon1.chartF3] using h3
  · simpa only [N6.Dcolon1.chartD] using hs
#print axioms N6.KroneckerCheck.check
#print axioms payload
#print axioms generic_vanish
#print axioms chart_vanish
end N6.Quartics21.Case008

namespace N6.Quartics21.Case009
open N6.SparseCheck N6.KroneckerCheck
theorem packed_ok : pairs (pack rad width) factorPairs = 0 :=
  (N6.KroneckerFastPack.pairs_fastPack_eq rad width 16 factorPairs).symm.trans fast_ok
theorem payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) factorPairs = 0 :=
  N6.KroneckerCheck.check x rad width factorPairs room_ok mass_ok packed_ok
theorem generic_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0) : value x gData = 0 := by
  have h := payload x
  simp only [factorPairs, pairs, h0, h1, h2, h3, mul_zero, add_zero, zero_add, scaledD, value_mapMul] at h
  apply N6.Saturation.cancel_D (x 0) (x 4) (value x N6.Dcolon1.dData) _ hs
  apply N6.Certificate.int_scaled_zero 2827272002717812869345148249411800 (by decide)
  simpa [scalarTerm, monVal, mul_assoc] using h
theorem chart_vanish {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (h0 : N6.Chart.F0 (x 4) (x 3) (x 2) (x 1) = 0)
    (h1 : N6.Chart.F1 (x 4) (x 3) (x 2) (x 1) = 0)
    (h2 : N6.Chart.F2 (x 4) (x 3) (x 2) (x 1) = 0)
    (h3 : N6.Chart.F3 (x 4) (x 3) (x 2) (x 1) = 0)
    (hs : x 0 * x 4 * N6.Chart.D (x 4) (x 3) (x 2) (x 1) - 1 = 0) : value x gData = 0 := by
  apply generic_vanish x
  · simpa only [N6.Dcolon1.chartF0] using h0
  · simpa only [N6.Dcolon1.chartF1] using h1
  · simpa only [N6.Dcolon1.chartF2] using h2
  · simpa only [N6.Dcolon1.chartF3] using h3
  · simpa only [N6.Dcolon1.chartD] using hs
#print axioms N6.KroneckerCheck.check
#print axioms payload
#print axioms generic_vanish
#print axioms chart_vanish
end N6.Quartics21.Case009

namespace N6.Quartics21.Case010
open N6.SparseCheck N6.KroneckerCheck
theorem packed_ok : pairs (pack rad width) factorPairs = 0 :=
  (N6.KroneckerFastPack.pairs_fastPack_eq rad width 16 factorPairs).symm.trans fast_ok
theorem payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) factorPairs = 0 :=
  N6.KroneckerCheck.check x rad width factorPairs room_ok mass_ok packed_ok
theorem generic_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0) : value x gData = 0 := by
  have h := payload x
  simp only [factorPairs, pairs, h0, h1, h2, h3, mul_zero, add_zero, zero_add, scaledD, value_mapMul] at h
  apply N6.Saturation.cancel_D (x 0) (x 4) (value x N6.Dcolon1.dData) _ hs
  apply N6.Certificate.int_scaled_zero 2827272002717812869345148249411800 (by decide)
  simpa [scalarTerm, monVal, mul_assoc] using h
theorem chart_vanish {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (h0 : N6.Chart.F0 (x 4) (x 3) (x 2) (x 1) = 0)
    (h1 : N6.Chart.F1 (x 4) (x 3) (x 2) (x 1) = 0)
    (h2 : N6.Chart.F2 (x 4) (x 3) (x 2) (x 1) = 0)
    (h3 : N6.Chart.F3 (x 4) (x 3) (x 2) (x 1) = 0)
    (hs : x 0 * x 4 * N6.Chart.D (x 4) (x 3) (x 2) (x 1) - 1 = 0) : value x gData = 0 := by
  apply generic_vanish x
  · simpa only [N6.Dcolon1.chartF0] using h0
  · simpa only [N6.Dcolon1.chartF1] using h1
  · simpa only [N6.Dcolon1.chartF2] using h2
  · simpa only [N6.Dcolon1.chartF3] using h3
  · simpa only [N6.Dcolon1.chartD] using hs
#print axioms N6.KroneckerCheck.check
#print axioms payload
#print axioms generic_vanish
#print axioms chart_vanish
end N6.Quartics21.Case010

namespace N6.Quartics21.Case011
open N6.SparseCheck N6.KroneckerCheck
theorem packed_ok : pairs (pack rad width) factorPairs = 0 :=
  (N6.KroneckerFastPack.pairs_fastPack_eq rad width 16 factorPairs).symm.trans fast_ok
theorem payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) factorPairs = 0 :=
  N6.KroneckerCheck.check x rad width factorPairs room_ok mass_ok packed_ok
theorem generic_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0) : value x gData = 0 := by
  have h := payload x
  simp only [factorPairs, pairs, h0, h1, h2, h3, mul_zero, add_zero, zero_add, scaledD, value_mapMul] at h
  apply N6.Saturation.cancel_D (x 0) (x 4) (value x N6.Dcolon1.dData) _ hs
  apply N6.Certificate.int_scaled_zero 353409000339726608668143531176475 (by decide)
  simpa [scalarTerm, monVal, mul_assoc] using h
theorem chart_vanish {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (h0 : N6.Chart.F0 (x 4) (x 3) (x 2) (x 1) = 0)
    (h1 : N6.Chart.F1 (x 4) (x 3) (x 2) (x 1) = 0)
    (h2 : N6.Chart.F2 (x 4) (x 3) (x 2) (x 1) = 0)
    (h3 : N6.Chart.F3 (x 4) (x 3) (x 2) (x 1) = 0)
    (hs : x 0 * x 4 * N6.Chart.D (x 4) (x 3) (x 2) (x 1) - 1 = 0) : value x gData = 0 := by
  apply generic_vanish x
  · simpa only [N6.Dcolon1.chartF0] using h0
  · simpa only [N6.Dcolon1.chartF1] using h1
  · simpa only [N6.Dcolon1.chartF2] using h2
  · simpa only [N6.Dcolon1.chartF3] using h3
  · simpa only [N6.Dcolon1.chartD] using hs
#print axioms N6.KroneckerCheck.check
#print axioms payload
#print axioms generic_vanish
#print axioms chart_vanish
end N6.Quartics21.Case011

namespace N6.Quartics21.Case012
open N6.SparseCheck N6.KroneckerCheck
theorem packed_ok : pairs (pack rad width) factorPairs = 0 :=
  (N6.KroneckerFastPack.pairs_fastPack_eq rad width 16 factorPairs).symm.trans fast_ok
theorem payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) factorPairs = 0 :=
  N6.KroneckerCheck.check x rad width factorPairs room_ok mass_ok packed_ok
theorem generic_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0) : value x gData = 0 := by
  have h := payload x
  simp only [factorPairs, pairs, h0, h1, h2, h3, mul_zero, add_zero, zero_add, scaledD, value_mapMul] at h
  apply N6.Saturation.cancel_D (x 0) (x 4) (value x N6.Dcolon1.dData) _ hs
  apply N6.Certificate.int_scaled_zero 65750511691111927194073215102600 (by decide)
  simpa [scalarTerm, monVal, mul_assoc] using h
theorem chart_vanish {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (h0 : N6.Chart.F0 (x 4) (x 3) (x 2) (x 1) = 0)
    (h1 : N6.Chart.F1 (x 4) (x 3) (x 2) (x 1) = 0)
    (h2 : N6.Chart.F2 (x 4) (x 3) (x 2) (x 1) = 0)
    (h3 : N6.Chart.F3 (x 4) (x 3) (x 2) (x 1) = 0)
    (hs : x 0 * x 4 * N6.Chart.D (x 4) (x 3) (x 2) (x 1) - 1 = 0) : value x gData = 0 := by
  apply generic_vanish x
  · simpa only [N6.Dcolon1.chartF0] using h0
  · simpa only [N6.Dcolon1.chartF1] using h1
  · simpa only [N6.Dcolon1.chartF2] using h2
  · simpa only [N6.Dcolon1.chartF3] using h3
  · simpa only [N6.Dcolon1.chartD] using hs
#print axioms N6.KroneckerCheck.check
#print axioms payload
#print axioms generic_vanish
#print axioms chart_vanish
end N6.Quartics21.Case012

namespace N6.Quartics21.Case013
open N6.SparseCheck N6.KroneckerCheck
theorem packed_ok : pairs (pack rad width) factorPairs = 0 :=
  (N6.KroneckerFastPack.pairs_fastPack_eq rad width 16 factorPairs).symm.trans fast_ok
theorem payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) factorPairs = 0 :=
  N6.KroneckerCheck.check x rad width factorPairs room_ok mass_ok packed_ok
theorem generic_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0) : value x gData = 0 := by
  have h := payload x
  simp only [factorPairs, pairs, h0, h1, h2, h3, mul_zero, add_zero, zero_add, scaledD, value_mapMul] at h
  apply N6.Saturation.cancel_D (x 0) (x 4) (value x N6.Dcolon1.dData) _ hs
  apply N6.Certificate.int_scaled_zero 2827272002717812869345148249411800 (by decide)
  simpa [scalarTerm, monVal, mul_assoc] using h
theorem chart_vanish {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (h0 : N6.Chart.F0 (x 4) (x 3) (x 2) (x 1) = 0)
    (h1 : N6.Chart.F1 (x 4) (x 3) (x 2) (x 1) = 0)
    (h2 : N6.Chart.F2 (x 4) (x 3) (x 2) (x 1) = 0)
    (h3 : N6.Chart.F3 (x 4) (x 3) (x 2) (x 1) = 0)
    (hs : x 0 * x 4 * N6.Chart.D (x 4) (x 3) (x 2) (x 1) - 1 = 0) : value x gData = 0 := by
  apply generic_vanish x
  · simpa only [N6.Dcolon1.chartF0] using h0
  · simpa only [N6.Dcolon1.chartF1] using h1
  · simpa only [N6.Dcolon1.chartF2] using h2
  · simpa only [N6.Dcolon1.chartF3] using h3
  · simpa only [N6.Dcolon1.chartD] using hs
#print axioms N6.KroneckerCheck.check
#print axioms payload
#print axioms generic_vanish
#print axioms chart_vanish
end N6.Quartics21.Case013

namespace N6.Quartics21.Case014
open N6.SparseCheck N6.KroneckerCheck
theorem packed_ok : pairs (pack rad width) factorPairs = 0 :=
  (N6.KroneckerFastPack.pairs_fastPack_eq rad width 16 factorPairs).symm.trans fast_ok
theorem payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) factorPairs = 0 :=
  N6.KroneckerCheck.check x rad width factorPairs room_ok mass_ok packed_ok
theorem generic_vanish {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0) : value x gData = 0 := by
  have h := payload x
  simp only [factorPairs, pairs, h0, h1, h2, h3, mul_zero, add_zero, zero_add, scaledD, value_mapMul] at h
  apply N6.Saturation.cancel_D (x 0) (x 4) (value x N6.Dcolon1.dData) _ hs
  apply N6.Certificate.int_scaled_zero 2827272002717812869345148249411800 (by decide)
  simpa [scalarTerm, monVal, mul_assoc] using h
theorem chart_vanish {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (h0 : N6.Chart.F0 (x 4) (x 3) (x 2) (x 1) = 0)
    (h1 : N6.Chart.F1 (x 4) (x 3) (x 2) (x 1) = 0)
    (h2 : N6.Chart.F2 (x 4) (x 3) (x 2) (x 1) = 0)
    (h3 : N6.Chart.F3 (x 4) (x 3) (x 2) (x 1) = 0)
    (hs : x 0 * x 4 * N6.Chart.D (x 4) (x 3) (x 2) (x 1) - 1 = 0) : value x gData = 0 := by
  apply generic_vanish x
  · simpa only [N6.Dcolon1.chartF0] using h0
  · simpa only [N6.Dcolon1.chartF1] using h1
  · simpa only [N6.Dcolon1.chartF2] using h2
  · simpa only [N6.Dcolon1.chartF3] using h3
  · simpa only [N6.Dcolon1.chartD] using hs
#print axioms N6.KroneckerCheck.check
#print axioms payload
#print axioms generic_vanish
#print axioms chart_vanish
end N6.Quartics21.Case014

