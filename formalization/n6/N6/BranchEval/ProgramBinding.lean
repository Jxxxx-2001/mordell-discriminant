import N6.BranchEval.ProgramSoundness

set_option autoImplicit false

namespace N6.BranchEval.Program
open N6.SparseCheck

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- A reference, e.g. the saved Ay coordinate, is an atom. Interpret only the
    requested expression skeleton, not the expression that produced that atom. -/
noncomputable def exprValue (x : Fin 5 → R) (P : Table) : SourceExpr → R
  | .ref i => nodeValue x P i
  | .input j => meaning x (P.input j)
  | .lit z d => meaning x (litNF z d)
  | .add _ a b => exprValue x P a + exprValue x P b
  | .mul _ a b => exprValue x P a * exprValue x P b

theorem matchesExpr_sound (x : Fin 5 → R) (P : Table)
    (law : ∀ i < P.size, nodeValue x P i = opValue x P (P.row i).op)
    (e : SourceExpr) (i : Nat) (ok : matchesExpr P e i = true) :
    nodeValue x P i = exprValue x P e := by
  induction e generalizing i with
  | ref j =>
    have h : i=j ∧ i<P.size := of_decide_eq_true ok
    exact congrArg (nodeValue x P) h.1
  | input j =>
    have h : i<P.size ∧ (P.row i).op = .input j := of_decide_eq_true ok
    simpa only [h.2, opValue, exprValue] using law i h.1
  | lit z d =>
    have h : i<P.size ∧ (P.row i).op = .lit z d := of_decide_eq_true ok
    simpa only [h.2, opValue, exprValue] using law i h.1
  | add rev l r il ir =>
    cases ho : (P.row i).op with
    | input j => simp [matchesExpr, ho] at ok
    | lit z d => simp [matchesExpr, ho] at ok
    | mul a b => simp [matchesExpr, ho] at ok
    | add a b =>
      simp only [matchesExpr, ho, Bool.and_eq_true, decide_eq_true_eq] at ok
      have step := law i ok.1
      rw [ho] at step
      calc
        nodeValue x P i = nodeValue x P a + nodeValue x P b := step
        _ = nodeValue x P (if rev then b else a) + nodeValue x P (if rev then a else b) := by
            cases rev <;> simp [add_comm]
        _ = exprValue x P (.add rev l r) := congrArg₂ (· + ·) (il _ ok.2.1) (ir _ ok.2.2)
  | mul rev l r il ir =>
    cases ho : (P.row i).op with
    | input j => simp [matchesExpr, ho] at ok
    | lit z d => simp [matchesExpr, ho] at ok
    | add a b => simp [matchesExpr, ho] at ok
    | mul a b =>
      simp only [matchesExpr, ho, Bool.and_eq_true, decide_eq_true_eq] at ok
      have step := law i ok.1
      rw [ho] at step
      calc
        nodeValue x P i = nodeValue x P a * nodeValue x P b := step
        _ = nodeValue x P (if rev then b else a) * nodeValue x P (if rev then a else b) := by
            cases rev <;> simp [mul_comm]
        _ = exprValue x P (.mul rev l r) := congrArg₂ (· * ·) (il _ ok.2.1) (ir _ ok.2.2)

theorem checked_endpoint (x : Fin 5 → R) (P : Table) (hf : value x P.factor = 0)
    (checked : Checked P) (i j : Nat) (l r : SourceExpr)
    (leftBinding : matchesExpr P l i = true) (rightBinding : matchesExpr P r j = true)
    (sameNF : (P.row i).out = (P.row j).out) : exprValue x P l = exprValue x P r := by
  have eqns (k : Nat) (hk : k < P.size) := checkAt_sound x P k hf (checked k hk)
  have le := matchesExpr_sound x P eqns l i leftBinding
  have re := matchesExpr_sound x P eqns r j rightBinding
  exact le.symm.trans ((congrArg (meaning x) sameNF).trans re)

/-- Specialize an input atom to the actual coordinate using its proven projected
    numerator identity. This step does not assume a coordinate already equals its map. -/
theorem input_of_projection (x : Fin 5 → R) (a : NF) (y : R) (hd : a.den ≠ 0)
    (hy : (a.den : R)*y = value x a.num) : meaning x a = y :=
  N6.BranchEval.same_normal_form a.den hd (nf_invariant x a hd) hy.symm

#print axioms check_sound
#print axioms checked_endpoint
end N6.BranchEval.Program

