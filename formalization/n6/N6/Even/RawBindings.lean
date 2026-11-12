import N6.Even.CoverageSemantics
import N6.Chart

set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000

namespace N6.Even
open N6.SparseCheck N6.KroneckerCheck

section
variable {K : Type*} [Field K] [CharZero K]

def delta (c e : K) : K := c^2-4*c^3-4*e-27*e^2+18*c*e
def p6 (c : K) : K := (5*c-1)*(5*c^2+36*c-9)*(5*c^3-9*c^2+15*c-3)
def eGraph (c : K) : K := 225*c^5+1225*c^4-2584*c^3+5376*c^2-2013*c+207
def point (t c e : K) : Fin 5 → K := fun i =>
  if i.val=0 then t else if i.val=1 then c else if i.val=2 then e else 0

theorem E1_value (t c e : K) : value (point t c e) E1Data = N6.Chart.E1 0 c 0 e := by
  simp [E1Data, E1DataPart0, value_append, value, monVal, point, N6.Chart.E1] <;> ring

theorem E3_value (t c e : K) : value (point t c e) E3Data = N6.Chart.E3 0 c 0 e := by
  simp [E3Data, E3DataPart0, value_append, value, monVal, point, N6.Chart.E3] <;> ring

theorem S_value (t c e : K) : value (point t c e) SData = t*e*delta c e-1 := by
  simp [SData, SDataPart0, value_append, value, monVal, point, delta] <;> ring

theorem EvenP6_value (t c e : K) : value (point t c e) EvenP6Data = p6 c := by
  simp [EvenP6Data, EvenP6DataPart0, value_append, value, monVal, point, p6] <;> ring

theorem EvenEGraph_value (t c e : K) : value (point t c e) EvenEGraphData = 180*e-eGraph c := by
  simp [EvenEGraphData, EvenEGraphDataPart0, value_append, value, monVal, point, eGraph] <;> ring

theorem originalD_even (c e : K) :
    N6.Chart.originalD 0 c 0 e = 64*e*(delta c e)^2 := by
  simp [N6.Chart.originalD, delta] <;> ring

theorem sigma_ne_zero (c e : K) (hd : N6.Chart.originalD 0 c 0 e ≠ 0) :
    e*delta c e ≠ 0 := by
  intro hs
  apply hd
  rw [originalD_even]
  calc
    64*e*(delta c e)^2 = 64*delta c e*(e*delta c e) := by ring
    _ = 0 := by rw [hs, mul_zero]

theorem exists_saturation (c e : K) (hd : N6.Chart.originalD 0 c 0 e ≠ 0) :
    ∃ t : K, t*e*delta c e-1 = 0 := by
  have hs := sigma_ne_zero c e hd
  refine ⟨(e*delta c e)⁻¹, ?_⟩
  calc
    (e*delta c e)⁻¹*e*delta c e-1 = (e*delta c e)⁻¹*(e*delta c e)-1 := by ring
    _ = 0 := by rw [inv_mul_cancel₀ hs, sub_self]

theorem coverage_of_raw [Algebra ℚ K] (c e : K)
    (h1 : N6.Chart.E1 0 c 0 e = 0) (h3 : N6.Chart.E3 0 c 0 e = 0)
    (hd : N6.Chart.originalD 0 c 0 e ≠ 0) : p6 c = 0 ∧ 180*e-eGraph c = 0 := by
  obtain ⟨t, ht⟩ := exists_saturation c e hd
  have h := coverage_vanish (point t c e) ((E1_value t c e).trans h1)
    ((E3_value t c e).trans h3) ((S_value t c e).trans ht)
  simpa only [EvenP6_value, EvenEGraph_value] using h

#print axioms coverage_of_raw
end
end N6.Even
