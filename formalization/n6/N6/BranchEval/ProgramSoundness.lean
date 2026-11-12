import N6.BranchEval.ProgramCore
import N6.BranchEval.OperationSemantics
import review.SparseProductReduce

set_option autoImplicit false

namespace N6.BranchEval.Program
open N6.SparseCheck N6.KroneckerCheck

variable {R : Type*} [CommRing R] [Algebra ℚ R]

private theorem val_scale (x : Fin 5 → R) (c : Int) (p : Poly) :
    value x (coefScale c p) = (c : R)*value x p := by
  induction p with
  | nil => simp [coefScale, value]
  | cons a p ih =>
    simp only [coefScale, List.map_cons, value, Int.cast_mul] at ih ⊢
    rw [ih]
    ring

private theorem val_one (x : Fin 5 → R) : value x unitPoly = 1 := by
  simp [unitPoly, value, monVal]

/-- Each node is an opaque bounded-degree rational polynomial value, even when
    the operation graph represents a substitution of high formal degree. -/
noncomputable def meaning (x : Fin 5 → R) (a : NF) : R :=
  algebraMap ℚ R ((a.den : ℚ)⁻¹) * value x a.num

theorem nf_invariant (x : Fin 5 → R) (a : NF) (ha : a.den ≠ 0) :
    value x a.num = (a.den : R)*meaning x a := by
  have h : (a.den : R)*algebraMap ℚ R ((a.den : ℚ)⁻¹) = 1 := by
    have hr : (a.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
    simpa only [map_intCast] using
      (show algebraMap ℚ R (a.den : ℚ)*algebraMap ℚ R ((a.den : ℚ)⁻¹) = 1 by
        rw [← map_mul, mul_inv_cancel₀ hr, map_one])
  rw [meaning, ← mul_assoc, h, one_mul]

theorem literal_value (x : Fin 5 → R) (z d : Int) :
    meaning x (litNF z d) = algebraMap ℚ R ((d : ℚ)⁻¹) * (z : R) := by
  simp [meaning, litNF, val_scale, val_one]

noncomputable def nodeValue (x : Fin 5 → R) (P : Table) (i : Nat) : R :=
  meaning x (P.row i).out

noncomputable def opValue (x : Fin 5 → R) (P : Table) : Op → R
  | .input j => meaning x (P.input j)
  | .lit z d => meaning x (litNF z d)
  | .add a b => nodeValue x P a + nodeValue x P b
  | .mul a b => nodeValue x P a * nodeValue x P b

private theorem base_law (x : Fin 5 → R) (f : Poly) (r : Row) (a : NF)
    (hf : value x f = 0) (hs : r.scale ≠ 0) (ho : r.out.den ≠ 0) (ha : a.den ≠ 0)
    (ground : zero (N6.SparseProductReduce.reduceProducts (basePairs f r a)) = true) :
    meaning x r.out = meaning x a := by
  have h := N6.SparseProductReduce.pairs_vanish x _ ground
  simp only [basePairs, pairs, val_scale, val_one, Int.cast_mul, Int.cast_neg, hf, mul_one,
    neg_mul, mul_zero, zero_mul, add_zero] at h
  have residual : (r.scale : R)*((r.out.den : R)*value x a.num - (a.den : R)*value x r.out.num) = 0 := by
    linear_combination h
  have hres := N6.Certificate.int_scaled_zero r.scale hs _ residual
  rw [nf_invariant x a ha] at hres
  apply N6.BranchEval.same_normal_form r.out.den ho (nf_invariant x r.out ho)
  apply sub_eq_zero.mp
  apply N6.Certificate.int_scaled_zero a.den ha
  linear_combination -hres

private theorem add_law (x : Fin 5 → R) (f : Poly) (r : Row) (a b : NF)
    (hf : value x f = 0) (hs : r.scale ≠ 0) (ho : r.out.den ≠ 0)
    (ha : a.den ≠ 0) (hb : b.den ≠ 0)
    (ground : zero (N6.SparseProductReduce.reduceProducts (addPairs f r a b)) = true) :
    meaning x r.out = meaning x a + meaning x b := by
  have h := N6.SparseProductReduce.pairs_vanish x _ ground
  simp only [addPairs, pairs, val_scale, val_one, Int.cast_mul, Int.cast_neg, Int.cast_one,
    mul_one, add_zero] at h
  apply N6.BranchEval.same_normal_form r.out.den ho (nf_invariant x r.out ho)
  apply N6.BranchEval.add_gate r.scale a.den b.den r.out.den hs ha hb hf
    (nf_invariant x a ha) (nf_invariant x b hb) (q := value x r.quot)
  linear_combination h

private theorem mul_law (x : Fin 5 → R) (f : Poly) (r : Row) (a b : NF)
    (hf : value x f = 0) (hs : r.scale ≠ 0) (ho : r.out.den ≠ 0)
    (ha : a.den ≠ 0) (hb : b.den ≠ 0)
    (ground : zero (N6.SparseProductReduce.reduceProducts (mulPairs f r a b)) = true) :
    meaning x r.out = meaning x a * meaning x b := by
  have h := N6.SparseProductReduce.pairs_vanish x _ ground
  simp only [mulPairs, pairs, val_scale, val_one, Int.cast_mul, Int.cast_neg, Int.cast_one,
    mul_one, add_zero] at h
  apply N6.BranchEval.same_normal_form r.out.den ho (nf_invariant x r.out ho)
  apply N6.BranchEval.mul_gate r.scale a.den b.den r.out.den hs ha hb hf
    (nf_invariant x a ha) (nf_invariant x b hb) (q := value x r.quot)
  linear_combination h

theorem checkAt_sound (x : Fin 5 → R) (P : Table) (i : Nat) (hf : value x P.factor = 0)
    (ok : checkAt P i = true) :
    nodeValue x P i = opValue x P (P.row i).op := by
  obtain ⟨⟨hs,ho⟩,hop,hg⟩ := (show
    ((P.row i).scale ≠ 0 ∧ (P.row i).out.den ≠ 0) ∧
    opOK P i (P.row i).op = true ∧
    zero (N6.SparseProductReduce.reduceProducts (parts P (P.row i))) = true by
      simpa only [checkAt, Bool.and_eq_true, decide_eq_true_eq] using ok)
  cases he : (P.row i).op with
  | input j =>
    have h := of_decide_eq_true (show decide (j < P.inputSize ∧ (P.input j).den ≠ 0) = true by
      simpa only [he, opOK] using hop)
    exact base_law x P.factor (P.row i) (P.input j) hf hs ho h.2 (by simpa only [parts, he] using hg)
  | lit z d =>
    have h : d ≠ 0 := of_decide_eq_true (by simpa only [he, opOK] using hop)
    exact base_law x P.factor (P.row i) (litNF z d) hf hs ho h (by simpa only [parts, he] using hg)
  | add a b =>
    have h := of_decide_eq_true (show decide (a<i ∧ b<i ∧ (P.row a).out.den ≠ 0 ∧
      (P.row b).out.den ≠ 0) = true by simpa only [he, opOK] using hop)
    exact add_law x P.factor (P.row i) (P.row a).out (P.row b).out hf hs ho h.2.2.1 h.2.2.2 (by simpa only [parts, he] using hg)
  | mul a b =>
    have h := of_decide_eq_true (show decide (a<i ∧ b<i ∧ (P.row a).out.den ≠ 0 ∧
      (P.row b).out.den ≠ 0) = true by simpa only [he, opOK] using hop)
    exact mul_law x P.factor (P.row i) (P.row a).out (P.row b).out hf hs ho h.2.2.1 h.2.2.2 (by simpa only [parts, he] using hg)

theorem checked_slot {P : Table} {start count j : Nat} (ok : checkBlock P start count = true)
    (hj : j < count) : checkAt P (start+j) = true :=
  (List.all_eq_true.mp ok) j (List.mem_range.mpr hj)

abbrev Checked (P : Table) := ∀ i < P.size, checkAt P i = true

theorem check_sound (x : Fin 5 → R) (P : Table) (hf : value x P.factor = 0)
    (ok : Checked P) (i : Nat) (hi : i < P.size) :
    value x (P.row i).out.num = ((P.row i).out.den : R)*nodeValue x P i ∧
    nodeValue x P i = opValue x P (P.row i).op := by
  have hh := ok i hi
  have hden : (P.row i).out.den ≠ 0 := by
    simp only [checkAt, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  exact ⟨nf_invariant x _ hden, checkAt_sound x P i hf (ok i hi)⟩

end N6.BranchEval.Program

