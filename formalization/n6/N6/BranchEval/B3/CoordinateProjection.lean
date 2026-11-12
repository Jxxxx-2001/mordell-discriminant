import N6.BranchEval.B3.EndpointDefinitions
import N6.BranchEval.B3.ProjectionGround
import N6.Weighted49.ColumnHelpers
import N6.Weighted49.LexSemantics
import Mathlib.Tactic.LinearCombination
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B3.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
variable {K : Type*} [Field K] [CharZero K]
open scoped BigOperators
theorem projection_cH_value (x : Fin 5 → K) : value x projection_cH = ∑ i : Fin 35, (N6.Weighted49.lex_cH i : K)*x 4^i.val := by
  simp only [projection_cH, N6.Weighted49.value_polyLin, N6.Weighted49.W, monVal, pow_zero, one_mul]
theorem project_c (x : Fin 5 → K) (hf : value x program.factor = 0)
    (hy : N6.Weighted49.coordinate_c (x 4) (x 3) = 0) : C x = x 3 := by
  have h := N6.SparseProductReduce.pairs_vanish x projection_cPairs projection_cChecked
  simp only [projection_cPairs, pairs, value_coefScale, value_unitPoly, Int.cast_mul, Int.cast_neg, Int.cast_one, mul_one, hf, mul_zero, zero_mul, add_zero] at h
  have hr : (N6.Weighted49.lex_cA : K)*value x input1NF.num + (input1NF.den : K)*value x projection_cH = 0 := by
    apply N6.Certificate.int_scaled_zero projection_cL projection_cL_nonzero
    linear_combination h
  rw [projection_cH_value] at hr
  change (N6.Weighted49.lex_cA : K)*x 3 + _ = 0 at hy
  apply input_of_projection x input1NF (x 3) input1_den_ne_zero
  apply sub_eq_zero.mp
  apply N6.Certificate.int_scaled_zero N6.Weighted49.lex_cA projection_cA_nonzero
  linear_combination (input1NF.den : K)*hy - hr
#print axioms project_c
theorem projection_kH_value (x : Fin 5 → K) : value x projection_kH = ∑ i : Fin 35, (N6.Weighted49.lex_kH i : K)*x 4^i.val := by
  simp only [projection_kH, N6.Weighted49.value_polyLin, N6.Weighted49.W, monVal, pow_zero, one_mul]
theorem project_k (x : Fin 5 → K) (hf : value x program.factor = 0)
    (hy : N6.Weighted49.coordinate_k (x 4) (x 2) = 0) : Kcoord x = x 2 := by
  have h := N6.SparseProductReduce.pairs_vanish x projection_kPairs projection_kChecked
  simp only [projection_kPairs, pairs, value_coefScale, value_unitPoly, Int.cast_mul, Int.cast_neg, Int.cast_one, mul_one, hf, mul_zero, zero_mul, add_zero] at h
  have hr : (N6.Weighted49.lex_kA : K)*value x input2NF.num + (input2NF.den : K)*value x projection_kH = 0 := by
    apply N6.Certificate.int_scaled_zero projection_kL projection_kL_nonzero
    linear_combination h
  rw [projection_kH_value] at hr
  change (N6.Weighted49.lex_kA : K)*x 2 + _ = 0 at hy
  apply input_of_projection x input2NF (x 2) input2_den_ne_zero
  apply sub_eq_zero.mp
  apply N6.Certificate.int_scaled_zero N6.Weighted49.lex_kA projection_kA_nonzero
  linear_combination (input2NF.den : K)*hy - hr
#print axioms project_k
theorem projection_eH_value (x : Fin 5 → K) : value x projection_eH = ∑ i : Fin 35, (N6.Weighted49.lex_eH i : K)*x 4^i.val := by
  simp only [projection_eH, N6.Weighted49.value_polyLin, N6.Weighted49.W, monVal, pow_zero, one_mul]
theorem project_e (x : Fin 5 → K) (hf : value x program.factor = 0)
    (hy : N6.Weighted49.coordinate_e (x 4) (x 1) = 0) : E x = x 1 := by
  have h := N6.SparseProductReduce.pairs_vanish x projection_ePairs projection_eChecked
  simp only [projection_ePairs, pairs, value_coefScale, value_unitPoly, Int.cast_mul, Int.cast_neg, Int.cast_one, mul_one, hf, mul_zero, zero_mul, add_zero] at h
  have hr : (N6.Weighted49.lex_eA : K)*value x input3NF.num + (input3NF.den : K)*value x projection_eH = 0 := by
    apply N6.Certificate.int_scaled_zero projection_eL projection_eL_nonzero
    linear_combination h
  rw [projection_eH_value] at hr
  change (N6.Weighted49.lex_eA : K)*x 1 + _ = 0 at hy
  apply input_of_projection x input3NF (x 1) input3_den_ne_zero
  apply sub_eq_zero.mp
  apply N6.Certificate.int_scaled_zero N6.Weighted49.lex_eA projection_eA_nonzero
  linear_combination (input3NF.den : K)*hy - hr
#print axioms project_e
end N6.BranchEval.B3.ProgramData
