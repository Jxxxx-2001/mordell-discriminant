import N6.Weighted49.ArithmeticFoldCore
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Ring.Int.Defs

set_option autoImplicit false

namespace N6.Weighted49

theorem getD_scaleList (a : Int) (xs : List Int) (i : Nat) :
    (scaleList a xs).getD i 0 = a * xs.getD i 0 := by
  simpa only [scaleList, mul_zero] using
    (List.getD_map xs (0 : Int) (n := i) (fun z : Int => a*z))

theorem getD_addLists0 (xs ys : List Int) (i : Nat) :
    (addLists0 xs ys).getD i 0 = xs.getD i 0 + ys.getD i 0 := by
  induction xs generalizing ys i with
  | nil => simp [addLists0]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists0]
    | cons y ys =>
      cases i with
      | zero => simp only [addLists0, List.getD_cons_zero]
      | succ i => simpa only [addLists0, List.getD_cons_succ] using ih ys i

private theorem zero_sumInt (n : Nat) : sumInt (fun _ : Fin n => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sumInt, zero_add] using ih

private theorem padded_zero (n i : Nat) : (List.replicate n (0 : Int)).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq]

/-- Empty or short columns extend by zero. Extra columns after the last weight
    have no contribution. No matrix-shape hypotheses are needed for this rule. -/
theorem getD_foldColumns (n : Nat) (weights : List Int) (cols : List (List Int)) (i : Nat) :
    (foldColumns n weights cols).getD i 0 =
      sumInt (fun j : Fin weights.length => (cols.getD j.val []).getD i 0 * weights.getD j.val 0) := by
  induction weights generalizing cols with
  | nil => simp only [foldColumns, List.length_nil, padded_zero, sumInt]
  | cons w ws ih =>
    cases cols with
    | nil =>
      simp only [foldColumns, padded_zero, List.getD_nil, zero_mul, zero_sumInt]
    | cons c cs =>
      by_cases hw : w = 0
      · subst w
        simpa only [foldColumns, if_pos, List.length_cons, sumInt, Fin.val_zero, Fin.val_succ,
          List.getD_cons_zero, List.getD_cons_succ, mul_zero, zero_add] using ih cs
      · simp only [foldColumns, if_neg hw, List.length_cons, sumInt, Fin.val_zero, Fin.val_succ,
          List.getD_cons_zero, List.getD_cons_succ, getD_addLists0, getD_scaleList, ih]
        rw [mul_comm w]

theorem getD_fold_matVec {n : Nat} (weights : List Int) (cols : List (List Int))
    (h : weights.length = n) (i : Fin n) :
    (foldColumns n weights cols).getD i.val 0 =
      matVec (fun i j : Fin n => (cols.getD j.val []).getD i.val 0)
        (fun j => weights.getD j.val 0) i := by
  subst n
  exact getD_foldColumns _ weights cols i.val

theorem getD_arrayList {α : Type*} (xs : Array α) (i : Nat) (d : α) :
    xs.toList.getD i d = xs.getD i d := by
  simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

theorem getD_columnLists (cols : Array (Array Int)) (j i : Nat) :
    ((cols.toList.map Array.toList).getD j []).getD i 0 = (cols.getD j #[]).getD i 0 := by
  have hc := List.getD_map cols.toList (#[] : Array Int) (n := j) Array.toList
  change ((cols.toList.map Array.toList).getD j (#[] : Array Int).toList).getD i 0 = _
  rw [hc, getD_arrayList, getD_arrayList]

/-- Transfer an entire checked list equality to all indexed coordinate gates.
    The concrete matrix's list layout can usually be identified by reflexivity. -/
theorem array_gate {n : Nat} (a b : Int) (src dst : Array Int)
    (cols : Array (Array Int)) (columnLists : List (List Int))
    (layout : columnLists = cols.toList.map Array.toList) (size : src.size = n)
    (gate : scaleList a dst.toList = scaleList b (foldColumns n src.toList columnLists))
    (i : Fin n) :
    a * dst.getD i.val 0 =
      b * matVec (fun i j : Fin n => (cols.getD j.val #[]).getD i.val 0)
        (fun j => src.getD j.val 0) i := by
  have h := congrArg (fun xs : List Int => xs.getD i.val 0) gate
  have len : src.toList.length = n := by simpa using size
  change (scaleList a dst.toList).getD i.val 0 =
    (scaleList b (foldColumns n src.toList columnLists)).getD i.val 0 at h
  rw [getD_scaleList, getD_scaleList, getD_fold_matVec src.toList columnLists len i, layout] at h
  simpa only [getD_columnLists, getD_arrayList] using h

#print axioms array_gate
end N6.Weighted49


