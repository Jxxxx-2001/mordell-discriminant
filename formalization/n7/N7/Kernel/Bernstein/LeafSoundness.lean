import N7.Kernel.Bernstein.IntegerCube

set_option autoImplicit false
namespace N7.Kernel

/-- A tensor lower bound on an arbitrary real function over its entire closed box. -/
def TensorLower (f : (Fin 3 → ℝ) → ℝ) (b : ClosedBox 3) (p : RationalCube) : Prop :=
  ∀ x, b.Contains x → p.boxEval b x ≤ f x

theorem TensorLower.split {f : (Fin 3 → ℝ) → ℝ} {b : ClosedBox 3}
    {p : RationalCube} (h : TensorLower f b p) (hw : b.Widths)
    (hp : p.Shape 12 12 6) (axis : Fin 3) (right : Bool) (bits : ℕ) :
    TensorLower f (b.half axis right) ((p.splitAxis axis right).roundControls bits) := by
  intro x hx
  exact (RationalCube.rounded_split_boxEval_le p hp b hw axis right bits hx).trans
    (h x (ClosedBox.half_subset hw axis right hx))

theorem TensorLower.integer_step {f : (Fin 3 → ℝ) → ℝ} {b : ClosedBox 3}
    {p : FixedTensor.Cube} (h : TensorLower f b (FixedTensor.decode p))
    (hw : b.Widths) (hp : (FixedTensor.decode p).Shape 12 12 6)
    (axis : Fin 3) (right : Bool) :
    TensorLower f (b.half axis right) (FixedTensor.decode (FixedTransfer.step p axis right)) := by
  rw [FixedTransfer.step_decode]
  exact h.split hw hp axis right 80

theorem integer_decode_nonneg (p : FixedTensor.Cube) (h : IntegerCube.nonneg p = true) :
    (FixedTensor.decode p).nonnegCheck = true := by
  simp only [IntegerCube.nonneg, List.all_eq_true] at h
  simp only [FixedTensor.decode, RationalCube.nonnegCheck, List.all_map,
    List.all_eq_true, Function.comp_def]
  intro row hr col hc z hz
  apply decide_eq_true
  exact div_nonneg
    (by exact_mod_cast (of_decide_eq_true (h row hr col hc z hz) : (0 : Int) ≤ z))
    (by positivity)

/-- Integer nonnegativity and a proved tensor binding certify every point of a leaf. -/
theorem checkedLeaf {f : (Fin 3 → ℝ) → ℝ} {b : ClosedBox 3} {p : FixedTensor.Cube}
    (hw : b.Widths) (hlower : TensorLower f b (FixedTensor.decode p))
    (hcheck : IntegerCube.nonneg p = true) (x : Fin 3 → ℝ) (hx : b.Contains x) :
    0 ≤ f x := by
  apply le_trans ?_ (hlower x hx)
  exact RationalCube.bernEval_nonneg _ 12 12 6 (integer_decode_nonneg p hcheck)
    _ _ _ (ClosedBox.coord_unit hw hx 0) (ClosedBox.coord_unit hw hx 1)
    (ClosedBox.coord_unit hw hx 2)

#print axioms checkedLeaf
#print axioms TensorLower.integer_step
end N7.Kernel
